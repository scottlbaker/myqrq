
// qrq - High speed morse trainer, similar to the DOS classic "Rufz"
// Copyright (c) 2006-2013  Fabian Kurz
//
// This program is free software; you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation; either version 2 of the License, or (at your option) any later
// version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
// PARTICULAR PURPOSE.  See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
// Street, Fifth Floor, Boston, MA  02110-1301, USA.

#include <pthread.h>     // CW output will be in a separate thread
#include <ncurses.h>
#include <stdlib.h>
#include <string.h>
#include <libgen.h>      // basename
#include <ctype.h>
#include <time.h>
#include <sys/time.h>
#include <limits.h>      // PATH_MAX
#include <dirent.h>
#include <math.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>    // mkdir
#include <sys/types.h>
#include <errno.h>

#define PI       M_PI
#define SILENCE  0       // for the tone generator
#define SINE     1
#define SAWTOOTH 2
#define SQUARE   3

#ifndef DESTDIR
#   define DESTDIR "/usr"
#endif

#ifndef VERSION
#  define VERSION "0.0.0"
#endif

#include "pulseaudio.h"
typedef void *AUDIO_HANDLE;

// callsign array will be dynamically allocated
static char **calls = NULL;

const static char *codetable[] = {
  ".-",    "-...", "-.-.",  "-..",  ".",   "..-.",  "--.", "....",  "..",   ".---",
  "-.-",   ".-..", "--",  "-.",  "---",   ".--.",  "--.-", ".-.",  "...",   "-",   "..-","...-",
  ".--",   "-..-", "-.--",  "--..", "-----", ".----", "..---", "...--", "....-", ".....",
  "-....", "--...", "---..", "----."
};

static char cblist[100][PATH_MAX];              // List of available callbase files
static int  cbindex = 0;                        // callbase list index
static int  cbptr   = 0;                        // callbase pointer
static char mycall[15] = "DJ1YFK";              // mycall. will be read from qrqrc
static char dspdevice[PATH_MAX] = "/dev/dsp";   // will also be read from qrqrc
static int score = 0;                           // qrq score
static int sending_complete;                    // global lock for "enter" while sending
static int callnr = 0;                          // nr of actual call in attempt
static int initialspeed = 200;                  // initial speed. to be read from file
static int mincharspeed = 0;                    // min. char. speed, below: farnsworth
static int speed = 200;                         // current speed in cpm
static int maxspeed = 0;
static int freq = 800;                          // current cw sidetone freq
static int errornr = 0;                         // number of errors in attempt
static int p = 0;                               // position of cursor, relative to x
static int status = 1;                          // 1= attempt, 2=config
static int mode = 1;                            // 0 = overwrite, 1 = insert
static int j = 0;                               // counter etc.
static int constanttone = 0;                    // if 1 don't change the pitch
static int ctonefreq = 800;                     // if constanttone=1 use this freq
static int unlimitedrepeat = 0;                 // allow unlimited repeats
static int fixspeed = 0;                        // keep speed fixed, regardless of err
static int unlimitedattempt = 0;                // attempt with all calls  of the DB
static unsigned long int nrofcalls = 0;

static long long starttime = 0;
static long long endtime = 0;
static int mstime = 0;

long samplerate = 44100;
static long long_i;
static int waveform = SINE;             // waveform: (0 = none)
static char wavename[10] = "Sine    ";  // Name of the waveform
static double edge = 2.0;               // rise/fall time in milliseconds
static int ed;                          // risetime, normalized to samplerate
static short buffer[88200];
static int full_buf[882000];            // 20 second max buffer
static int full_bufpos = 0;

AUDIO_HANDLE dsp_fd;

static int display_toplist();
static int calc_score(char *realcall, char *input, int speed, char *output);
static int update_score();
static int show_error(char *realcall, char *wrongcall);
static int clear_display();
static int add_to_toplist(char *mycall, int score, int maxspeed);
static int read_config();
static int tonegen(int freq, int length, int waveform);
static void *morse(void *arg);
static int add_to_buf(void *data, int size);
static int readline(WINDOW *win, int y, int x, char *line, int i);
static void thread_fail(int j);
static int find_files();
static int statistics();
static int read_callbase();
static void select_callbase();
static long long get_ms();
static void help();
static void callbase_dialog();
static void parameter_dialog();
static int clear_parameter_display();
static void update_parameter_dialog();

pthread_t cwthread;            // thread for CW output, to enable
pthread_attr_t cwattr;         // keyboard reading at the same time

char rcfilename[PATH_MAX] = "";  // filename and path to qrqrc
char tlfilename[PATH_MAX] = "";  // filename and path to toplist
char cbfilename[PATH_MAX] = "";  // filename and path to callbase

char destdir[PATH_MAX] = "";

// create windows
WINDOW *top_w;                  // actual score
WINDOW *mid_w;                  // callsign history/mistakes
WINDOW *conf_w;                 // parameter config display
WINDOW *bot_w;                  // user input line
WINDOW *inf_w;                  // info window for param displ
WINDOW *right_w;                // highscore list/settings


int main(int argc, char *argv[]) {
  strcpy(destdir, DESTDIR);
  char abort = 0;
  char tmp[80] = "";
  char input[15] = "";
  int i = 0, j = 0, k = 0;
  char previouscall[80] = "";
  int previousfreq = 0;
  int f6pressed = 0;

  if (argc > 1)
    help();

  (void)initscr();
  cbreak();
  noecho();
  curs_set(FALSE);
  keypad(stdscr, TRUE);
  scrollok(stdscr, FALSE);

  printw("\nqrq v%s - by Fabian Kurz, DJ1YFK\n", VERSION);
  refresh();

  // search for toplist and qrqrc
  find_files();

  // buffer for audio
  for (long_i = 0; long_i < 88200; long_i++)
    buffer[long_i] = 0;

  // random seed
  srand((unsigned)time(NULL));

  // Initialize cwthread. We have to wait for the cwthread to finish before
  // the next cw output can be made, this will be done with pthread_join
  pthread_attr_init(&cwattr);
  pthread_attr_setdetachstate(&cwattr, PTHREAD_CREATE_JOINABLE);

  printw("\nReading configuration file qrqrc \n");
  read_config();

  // read the callsign database
  nrofcalls = read_callbase();
  printw("\nReading %d lines from: %s\n\n", nrofcalls, basename(cbfilename));
  printw("Press any key to continue...");

  refresh();
  getch();

  erase();
  refresh();

  top_w   = newwin( 4, 60,  0,  0);
  mid_w   = newwin(17, 60,  4,  0);
  conf_w  = newwin(17, 60,  4,  0);
  bot_w   = newwin( 3, 60, 21,  0);
  inf_w   = newwin( 3, 60, 21,  0);
  right_w = newwin(24, 20,  0, 60);

  werase(top_w);
  werase(mid_w);
  werase(conf_w);
  werase(bot_w);
  werase(inf_w);
  werase(right_w);

  keypad(bot_w,  TRUE);
  keypad(mid_w,  TRUE);
  keypad(conf_w, TRUE);

  // the first thread call
  pthread_create(&cwthread, NULL, &morse, (void *)"");

  // run forever
  while (1) {
    while (status == 1) {
      box(top_w, 0, 0);
      box(conf_w, 0, 0);
      box(mid_w, 0, 0);
      box(bot_w, 0, 0);
      box(inf_w, 0, 0);
      box(right_w, 0, 0);
      wattron(top_w, A_BOLD);
      mvwaddstr(top_w, 1, 1, "QRQ v");
      mvwaddstr(top_w, 1, 6, VERSION);
      wattroff(top_w, A_BOLD);
      mvwaddstr(top_w, 1, 11, " by Fabian Kurz, DJ1YFK");
      mvwaddstr(top_w, 2, 1, "Homepage: http://fkurz.net/ham/qrq.html     ");
      clear_display();
      wattron(mid_w, A_BOLD);
      mvwaddstr(mid_w, 1, 1, "Usage:");
      wattroff(mid_w, A_BOLD);
      mvwaddstr(mid_w,  2, 2, "After entering your callsign, random callsigns");
      mvwaddstr(mid_w,  3, 2, "from a database will be sent. After each callsign,");
      mvwaddstr(mid_w,  4, 2, "enter what you have heard. If you copied correctly,");
      mvwaddstr(mid_w,  5, 2, "full points are credited and the speed increases by");
      mvwaddstr(mid_w,  6, 2, "2 WpM -- otherwise the speed decreases and only a ");
      mvwaddstr(mid_w,  7, 2, "fraction of the points, depending on the number of");
      mvwaddstr(mid_w,  8, 2, "errors is credited.");
      mvwaddstr(mid_w, 11, 2, "F6 repeats a callsign");
      mvwaddstr(mid_w, 12, 2, "Settings can be changed with F5 or in qrqrc");
      mvwaddstr(mid_w, 13, 2, "Score statistics (requires gnuplot) with F7");

      wattron(right_w, A_BOLD);
      mvwaddstr(right_w, 1, 6, "Toplist");
      wattroff(right_w, A_BOLD);
      display_toplist();
      p = 0;                    // cursor to start position
      wattron(bot_w, A_BOLD);
      mvwaddstr(bot_w, 1, 1, "Please enter your callsign                       ");
      wattroff(bot_w, A_BOLD);
      wrefresh(top_w);
      wrefresh(mid_w);
      wrefresh(bot_w);
      wrefresh(right_w);
      maxspeed = errornr = score = 0;
      speed = initialspeed;

      // prompt for own callsign
      i = readline(bot_w, 1, 30, mycall, 1);

      // F5 -> configuration
      if (i == 5) {
        parameter_dialog();
        break;
      }
      // F6 -> play test CW
      else if (i == 6) {
        freq = constanttone ? ctonefreq : 800;
        pthread_join(cwthread, NULL);
        j = pthread_create(&cwthread, NULL, &morse, (void *)"VVVTEST");
        thread_fail(j);
        break;
      } else if (i == 7) {
        statistics();
        break;
      }

      if (strlen(mycall) == 0)
        strcpy(mycall, "NOCALL");
      else if (strlen(mycall) > 7)      // cut excessively long calls
        mycall[7] = '\0';

      clear_display();
      wrefresh(mid_w);

      // update toplist (highlight may change)
      display_toplist();

      mvwprintw(top_w, 1, 1, "                                      ");
      mvwprintw(top_w, 2, 1, "                                               ");
      wattron(top_w, A_BOLD);
      mvwprintw(top_w, 1, 1, "%s", mycall);
      wattroff(top_w, A_BOLD);
      update_score();
      wrefresh(top_w);

      // re-read the callbase
      nrofcalls = read_callbase();

      for (callnr = 1; callnr < (unlimitedattempt ? nrofcalls : 51); callnr++) {
        // wait for the cwthread of the previous callsign
        pthread_join(cwthread, NULL);
        // select an unused callsign from the calls-array
        do
          i = (int)((float)nrofcalls * rand() / (RAND_MAX + 1.0));
        while (calls[i] == NULL);

        // only relevant for callbases with less than 50 calls
        if (nrofcalls == callnr)        // Only one call left!"
          callnr = 51;                  // Get out after next one

        // output frequency handling a) random b) fixed
        if (constanttone == 0)
          // random freq (fraction of samplerate)
          freq = (int)(samplerate / (50 + (40.0 * rand() / (RAND_MAX + 1.0))));
        else
          // fixed frequency
          freq = ctonefreq;

        mvwprintw(bot_w, 1, 1, "                                      ");
        mvwprintw(bot_w, 1, 1, "%3d/%s", callnr, unlimitedattempt ? "-" : "50");
        wrefresh(bot_w);
        tmp[0] = '\0';

        // starting the morse output in a separate process to make keyboard
        // input and echoing at the same time possible
        sending_complete = 0;
        j = pthread_create(&cwthread, NULL, morse, calls[i]);
        thread_fail(j);
        f6pressed = 0;

        // check for function key press
        while (!abort && (j = readline(bot_w, 1, 8, input, 1)) > 4) {
          switch (j) {
          case 6:              // repeat call
            if (f6pressed && (unlimitedrepeat == 0)) continue;
            f6pressed = 1;
            // wait for old cwthread to finish, then send call again
            pthread_join(cwthread, NULL);
            j = pthread_create(&cwthread, NULL, &morse, calls[i]);
            thread_fail(j);
            break;
          case 7:              // repeat previous call
            if (callnr > 1) {
              k = freq;
              freq = previousfreq;
              pthread_join(cwthread, NULL);
              j = pthread_create(&cwthread, NULL, &morse, previouscall);
              thread_fail(j);
              // wait for the CW thread before restore freq
              // this blocks keyboard input
              pthread_join(cwthread, NULL);
              freq = k;
            }
            break;
          case 10:             // abort
            abort = 1;
            break;
          default:
            break;
          }
        }

        if (abort) {
          endwin();
          exit(0);
        }

        tmp[0] = '\0';
        endtime = get_ms();
        score += calc_score(calls[i], input, speed, tmp);
        update_score();
        if (strcmp(tmp, "*"))           // made an error
          show_error(calls[i], tmp);
        input[0] = '\0';
        strncpy(previouscall, calls[i], 80);
        previousfreq = freq;
        calls[i] = NULL;
      }

      // attempt is over, send AR
      callnr = 0;
      pthread_join(cwthread, NULL);
      j = pthread_create(&cwthread, NULL, &morse, (void *)"+");
      thread_fail(j);
      add_to_toplist(mycall, score, maxspeed);

      curs_set(0);
      wattron(bot_w, A_BOLD);
      mvwprintw(bot_w, 1, 1, "Attempt finished. Press any key to continue!");
      wattroff(bot_w, A_BOLD);
      wrefresh(bot_w);
      getch();
      mvwprintw(bot_w, 1, 1, "                                            ");
      curs_set(1);
    }
  }

  getch();
  endwin();
  delwin(top_w);
  delwin(bot_w);
  delwin(mid_w);
  delwin(right_w);
  getch();
  return 0;
}

// Change parameters
void parameter_dialog() {
  int j = 0;

  update_parameter_dialog();

  while ((j = getch()) != 0) {
    switch ((int)j) {
    case '+':                               // rise/falltime
      if (edge <= 9.0)
        edge += 0.1;
      break;
    case '-':
      if (edge > 0.1)
        edge -= 0.1;
      break;
    case 'w':                               // change waveform
      waveform = ((waveform + 1) % 3) + 1;  // toggle 1-2-3
      break;
    case 'k':                               // constanttone
      if (ctonefreq >= 160)
        ctonefreq -= 10;
      else
        constanttone = 0;
      break;
    case 'l':
      if (constanttone == 0)
        constanttone = 1;
      else if (ctonefreq < 1600)
        ctonefreq += 10;
      break;
    case '0':
      if (constanttone == 1)
        constanttone = 0;
      else
        constanttone = 1;
      break;
    case 'f':
      unlimitedrepeat = (unlimitedrepeat ? 0 : 1);
      break;
    case 's':
      fixspeed = (fixspeed ? 0 : 1);
      break;
    case 'u':
      unlimitedattempt = (unlimitedattempt ? 0 : 1);
      break;
    case KEY_UP:
      initialspeed += 10;
      break;
    case KEY_DOWN:
      if (initialspeed > 10)
        initialspeed -= 10;
      break;
    case KEY_RIGHT:
      mincharspeed += 10;
      break;
    case KEY_LEFT:
      if (mincharspeed > 10)
        mincharspeed -= 10;
      break;
    case 'c':
      readline(conf_w, 5, 25, mycall, 1);
      if (strlen(mycall) == 0)
        strcpy(mycall, "NOCALL");
      else if (strlen(mycall) > 7)          // cut excessively long calls
        mycall[7] = '\0';
      p = 0;                                // cursor position
      break;
    case 'd':                               // go to database browser
        curs_set(1);
        callbase_dialog();
      break;
    case KEY_F(6):
      freq = constanttone ? ctonefreq : 800;
      pthread_join(cwthread, NULL);
      j = pthread_create(&cwthread, NULL, &morse, (void *)"TESTING");
      thread_fail(j);
      break;
    case KEY_F(1):
    case KEY_F(2):
    case KEY_F(3):
      curs_set(1);
      clear_parameter_display();
      wrefresh(conf_w);
      // restore old windows
      touchwin(top_w);
      touchwin(mid_w);
      touchwin(bot_w);
      touchwin(right_w);
      wrefresh(top_w);
      wrefresh(mid_w);
      wrefresh(bot_w);
      wrefresh(right_w);
      return;
    }
    speed = initialspeed;
    update_parameter_dialog();
  }
}


// update_parameter_dialog
// repaints the whole config/parameter screen (F5)
void update_parameter_dialog() {
  clear_parameter_display();
  switch (waveform) {
  case SINE:
    strcpy(wavename, "Sine    ");
    break;
  case SAWTOOTH:
    strcpy(wavename, "Sawtooth");
    break;
  case SQUARE:
    strcpy(wavename, "Square  ");
    break;
  }

  mvwaddstr(inf_w, 1, 1, "                                                         ");
  curs_set(0);
  wattron(conf_w, A_BOLD);
  mvwaddstr(conf_w, 1, 1, "Configuration:          Value                Change");
  wattroff(conf_w, A_BOLD);
  mvwprintw(conf_w, 2, 2, "Initial Speed:         %3d CpM / %3d WpM"
            "    up/down", initialspeed, initialspeed / 5);
  mvwprintw(conf_w, 3, 2, "Min. character Speed:  %3d CpM / %3d WpM"
            "    left/right", mincharspeed, mincharspeed / 5);
  mvwprintw(conf_w, 4, 2, "CW rise/falltime (ms): %1.1f           "
            "       +/-", edge);
  mvwprintw(conf_w, 5, 2, "Callsign:              %-14s"
            "       c", mycall);
  mvwprintw(conf_w, 6, 2, "CW pitch (0 = random): %-4d"
            "                 k/l or 0", (constanttone) ? ctonefreq : 0);
  mvwprintw(conf_w, 7, 2, "CW waveform:           %-8s"
            "             w", wavename);
  mvwprintw(conf_w, 8, 2, "Unlimited repeat:      %-3s"
            "                  f", (unlimitedrepeat ? "yes" : "no"));
  mvwprintw(conf_w, 9, 2, "Fixed CW speed:        %-3s"
            "                  s", (fixspeed ? "yes" : "no"));
  mvwprintw(conf_w, 10, 2, "Unlimited attempt:     %-3s"
            "                  u", (unlimitedattempt ? "yes" : "no"));
  mvwprintw(conf_w, 11, 2, "callbase:  %-15s"
            "   d (%d)", basename(cbfilename), nrofcalls);

  mvwprintw(conf_w, 14, 2, "Press F1 to go back");
  wrefresh(conf_w);
  wrefresh(inf_w);
}


void callbase_dialog() {
  clear_parameter_display();
  wattron(conf_w, A_BOLD);
  mvwaddstr(conf_w, 1, 1, "Change Callsign Database");
  wattroff(conf_w, A_BOLD);
  select_callbase();
  wrefresh(conf_w);
  return;
}


// read callsign data
static int readline(WINDOW *win, int y, int x, char *line, int capitals) {
  int c;
  int i = 0;

  if (strlen(line) == 0) p = 0;   // cursor to start if no call in buffer

  if (mode == 1)
    mvwaddstr(win, 1, 55, "INS");
  else
    mvwaddstr(win, 1, 55, "OVR");

  mvwaddstr(win, y, x, line);
  wmove(win, y, x + p);
  wrefresh(win);
  curs_set(TRUE);

  while (1) {
    c = wgetch(win);
    if (c == '\n' && sending_complete)
      break;

    if (((c > 64 && c < 91) || (c > 96 && c < 123) || (c > 47 && c < 58)
         || c == '/') && strlen(line) < 14) {
      line[strlen(line) + 1] = '\0';
      if (capitals)
        c = toupper(c);
      if (mode == 1) {                       // insert
        for (i = strlen(line); i > p; i--)   // move all chars by one
          line[i] = line[i - 1];
      }
      line[p] = c;                           // insert into gap
      p++;
    } else if ((c == KEY_BACKSPACE || c == 127 || c == 9 || c == 8)
               && p != 0) {                             // BACKSPACE
      for (i = p - 1; i < strlen(line); i++)
        line[i] = line[i + 1];
      p--;
    } else if (c == KEY_DC && strlen(line) != 0) {      // DELETE
      p++;
      for (i = p - 1; i < strlen(line); i++)
        line[i] = line[i + 1];
      p--;
    } else if (c == KEY_LEFT && p != 0) {
      p--;
    } else if (c == KEY_RIGHT && p < strlen(line)) {
      p++;
    } else if (c == KEY_HOME) {
      p = 0;
    } else if (c == KEY_END) {
      p = strlen(line);
    } else if (c == KEY_IC) {                           // INS/OVR
      if (mode == 1) {
        mode = 0;
        mvwaddstr(win, 1, 55, "OVR");
      } else {
        mode = 1;
        mvwaddstr(win, 1, 55, "INS");
      }
    } else if (c == KEY_F(5)) {
      parameter_dialog();
    // alias a bunch of keys to F6 (repeat callsign)
    // for convenience
    } else if ((c == KEY_LEFT)  || (c == KEY_RIGHT) ||
               (c == KEY_DOWN)  || (c == KEY_UP)    ||
               (c == KEY_PPAGE) || (c == KEY_NPAGE) ||
               (c == KEY_HOME)  || (c == KEY_END)   ||
               (c == KEY_DC)    || (c == KEY_F(1))  ||
               (c == KEY_F(2))  || (c == KEY_F(3))  ||
               (c == KEY_F(4))  || (c == KEY_F(6))) {
      return 6;
    } else if (c == KEY_F(7)) {
      return 7;
    } else if (c == KEY_F(10)) {                // quit
      if (callnr)                               // quit attempt only
        return 10;
      // else: quit program
      endwin();
      printf("Thanks for using 'qrq'!\nYou can submit your"
             " highscore to http://fkurz.net/ham/qrqtop.php\n");
      // make sure that no more output is running, then send 73 & quit
      speed = 200; freq = 800;
      pthread_join(cwthread, NULL);
      j = pthread_create(&cwthread, NULL, &morse, (void *)"73");
      thread_fail(j);
      // make sure the cw thread doesn't die with the main thread
      // Exit the whole main thread
      pthread_join(cwthread, NULL);
      exit(0);
    }
    mvwaddstr(win, y, x, "                ");
    mvwaddstr(win, y, x, line);
    wmove(win, y, x + p);
    wrefresh(win);
  }
  curs_set(FALSE);
  return 0;
}

// Read toplist and diplay first 10 entries
static int display_toplist() {
  FILE *fh;
  int i = 0;
  char tmp[35] = "";

  if ((fh = fopen(tlfilename, "a+")) == NULL) {
    endwin();
    fprintf(stderr, "Couldn't read or create file '%s'!", tlfilename);
    exit(EXIT_FAILURE);
  }
  rewind(fh);                        // go to beginning of file
  (void)fgets(tmp, 34, fh);          // skip the first line
  while ((feof(fh) == 0) && i < 20) {
    i++;
    if (fgets(tmp, 34, fh) != NULL) {
      tmp[17] = '\0';
      if (strstr(tmp, mycall))       // highlight own call
        wattron(right_w, A_BOLD);
      mvwaddstr(right_w, i + 2, 2, tmp);
      wattroff(right_w, A_BOLD);
    }
  }
  fclose(fh);
  wrefresh(right_w);
  return 0;
}

// calculate score depending on number of errors and speed
// writes the correct call and entered call with highlighted errors
// and returns the score for this call. There are no points
// in training modes (unlimited attempts/repeats, or fixed speed)
static int calc_score(char *realcall, char *input, int spd, char *output) {
  int i, x, m = 0;

  x = strlen(realcall);

  if (strcmp(input, realcall) == 0) {       // exact match!
    output[0] = '*';                        // * == OK, no mistake
    output[1] = '\0';
    if (speed > maxspeed) maxspeed = speed;
    if (!fixspeed) speed += 10;
    return 2 * x * spd;                     // score
  } else {                                  // assemble error string
    errornr += 1;
    if (strlen(input) >= x) x = strlen(input);
    for (i = 0; i < x; i++) {
      if (realcall[i] != input[i]) {
        m++;                                // mistake!
        output[i] = tolower(input[i]);      // print as lower case
      } else {
        output[i] = input[i];
      }
    }
    output[i] = '\0';
    if ((speed > 29) && !fixspeed) speed -= 10;

    // score when 1-3 mistakes made
    if (m < 4)
      return (int)(2 * x * spd) / (5 * m);
    else return 0; ;
  }
}

// print score, current speed and max speed to window
static int update_score() {
  mvwaddstr(top_w, 1, 10, "Score:                         ");
  mvwprintw(top_w, 2, 10, "File:  %s", basename(cbfilename));
  if (endtime > starttime) {
    mstime = (int)(endtime - starttime);
    mvwprintw(top_w, 1, 17, "%6d   %6d ms", score, mstime);
  } else {
    mvwprintw(top_w, 1, 17, "%6d", score);
  }
  wrefresh(top_w);
  return 0;
}

// Display the correct callsign and what the user entered
// with mistakes highlighted
static int show_error(char *realcall, char *wrongcall) {
  int x = 2;
  int y = errornr;
  int i;

  // if the screen is full of errors
  // remove them and start at the beginning
  if (errornr == 31) {
    for (i = 1; i < 16; i++)
      mvwaddstr(mid_w, i, 2, "                                        "
                "          ");
    errornr = y = 1;
  }
  // Move to second column after 15 errors
  if (errornr > 15) {
    x = 30; y = (errornr % 16) + 1;
  }
  mvwprintw(mid_w, y, x, "%-13s %-13s", realcall, wrongcall);
  wrefresh(mid_w);
  return 0;
}


// clear error display
static int clear_display() {
  int i;
  for (i = 1; i < 16; i++)
    mvwprintw(mid_w, i, 1, "                                 "
              "                        ");
  return 0;
}


// clear parameter display
static int clear_parameter_display() {
  int i;

  for (i = 1; i < 16; i++)
    mvwprintw(conf_w, i, 1, "                                 "
              "                        ");
  return 0;
}


// write entry into toplist at the right place
static int add_to_toplist(char *mycall, int score, int maxspeed) {
  FILE *fh;
  char *part1, *part2;
  char tmp[35] = "";
  char insertline[35] = "DJ1YFK     36666 333 1111111111";
  int i = 0, k = 0, j = 0;
  int pos = 0;          // position where first score < our score
  int timestamp = 0;
  int len = 32;         // length of a line

  // For the training modes
  if (score == 0)
    return 0;

  timestamp = (int)time(NULL);
  sprintf(insertline, "%-10s%6d %3d %10d", mycall, score, maxspeed, timestamp);

  if ((fh = fopen(tlfilename, "rb+")) == NULL) {
    printf("Unable to open toplist file %s!\n", tlfilename);
    exit(EXIT_FAILURE);
  }

  // find out if we use CRLF or just LF
  fgets(tmp, 35, fh);
  if (tmp[31] == '\r') {
    len = 33;
    strcat(insertline, "\r\n");
  } else {
    len = 32;
    strcat(insertline, "\n");
  }

  fseek(fh, 0, SEEK_END);
  j = ftell(fh);
  part1 = malloc((size_t)j);
  part2 = malloc((size_t)j + len);     // one additional entry
  rewind(fh);

  // read whole toplist
  fread(part1, sizeof(char), (size_t)j, fh);

  // find first score below "score"; scores at positions 10 + (i*len)
  do {
    for (i = 0; i < 6; i++)
      tmp[i] = part1[i + (10 + pos * len)];
    k = atoi(tmp);
    pos++;
  } while (score < k);

  // Found it! Insert score here!
  memcpy(part2, part1, len * (pos - 1));
  memcpy(part2 + len * (pos - 1), insertline, len);
  memcpy(part2 + len * pos, part1 + len * (pos - 1), j - len * (pos - 1));

  rewind(fh);
  fwrite(part2, sizeof(char), (size_t)j + len, fh);
  fclose(fh);
  free(part1);
  free(part2);
  return 0;
}


// Read config file
static int read_config() {
  FILE *fh;
  char tmp[80] = "";
  int i = 0;
  int k = 0;
  int line = 0;

  if ((fh = fopen(rcfilename, "r")) == NULL) {
    endwin();
    fprintf(stderr, "Unable to open config file %s!\n", rcfilename);
    exit(EXIT_FAILURE);
  }

  while ((feof(fh) == 0) && (fgets(tmp, 80, fh) != NULL)) {
    i = 0;
    line++;
    tmp[strlen(tmp) - 1] = '\0';

    // find callsign, speed etc.
    // only allow if the lines are beginning at zero
    if (tmp == strstr(tmp, "callsign=")) {
      while (isalnum(tmp[i] = toupper(tmp[9 + i])))
        i++;
      tmp[i] = '\0';
      if (strlen(tmp) < 8) {            // empty call allowed
        strcpy(mycall, tmp);
        printw("  line  %2d: callsign: %s\n", line, mycall);
      } else {
        printw("  line  %2d: callsign: %s too long. "
               "Using default >%s<.\n", line, tmp, mycall);
      }
    } else if (tmp == strstr(tmp, "initialspeed=")) {
      while (isdigit(tmp[i] = tmp[13 + i]))
        i++;
      tmp[i] = '\0';
      i = atoi(tmp);
      if (i > 9) {
        initialspeed = speed = i;
        printw("  line  %2d: initial speed: %d\n", line, initialspeed);
      } else {
        printw("  line  %2d: initial speed: %d invalid (range: 10..oo)."
               " Using default %d.\n", line, i, initialspeed);
      }
    } else if (tmp == strstr(tmp, "mincharspeed=")) {
      while (isdigit(tmp[i] = tmp[13 + i]))
        i++;
      tmp[i] = '\0';
      if ((i = atoi(tmp)) > 0) {
        mincharspeed = i;
        printw("  line  %2d: min char speed: %d\n", line, mincharspeed);
      }
    } else if (tmp == strstr(tmp, "dspdevice=")) {
      while (isgraph(tmp[i] = tmp[10 + i]))
        i++;
      tmp[i] = '\0';
      if (strlen(tmp) > 1) {
        strcpy(dspdevice, tmp);
        printw("  line  %2d: dspdevice: %s\n", line, dspdevice);
      } else {
        printw("  line  %2d: invalid dspdevice: %s "
               "Using default >%s<.\n", line, tmp, dspdevice);
      }
    } else if (tmp == strstr(tmp, "risetime=")) {
      while (isdigit(tmp[i] = tmp[9 + i]) || ((tmp[i] = tmp[9 + i])) == '.')
        i++;
      tmp[i] = '\0';
      edge = atof(tmp);
      printw("  line  %2d: risetime: %f\n", line, edge);
    } else if (tmp == strstr(tmp, "waveform=")) {
      if (isdigit(tmp[i] = tmp[9 + i])) {       // read 1 char only
        tmp[++i] = '\0';
        waveform = atoi(tmp);
      }
      if ((waveform <= 3) && (waveform > 0)) {
        printw("  line  %2d: waveform: %d\n", line, waveform);
      } else {
        printw("  line  %2d: waveform: %d invalid. Using default.\n",
               line, waveform);
        waveform = SINE;
      }
    } else if (tmp == strstr(tmp, "constanttone=")) {
      while (isdigit(tmp[i] = tmp[13 + i]))
        i++;
      tmp[i] = '\0';
      k = 0;
      k = atoi(tmp);                                // constanttone
      if ((k * k) > 1) {
        printw("  line  %2d: constant tone: %s invalid. "
               "Using default %d.\n", line, tmp, constanttone);
      } else {
        constanttone = k;
        printw("  line  %2d: constant tone: %d\n", line, constanttone);
      }
    } else if (tmp == strstr(tmp, "ctonefreq=")) {
      while (isdigit(tmp[i] = tmp[10 + i]))
        i++;
      tmp[i] = '\0';
      k = 0;
      k = atoi(tmp);                                // ctonefreq
      if ((k > 1600) || (k < 100)) {
        printw("  line  %2d: ctonefreq: %s invalid. "
               "Using default %d.\n", line, tmp, ctonefreq);
      } else {
        ctonefreq = k;
        printw("  line  %2d: CW tone (Hz): %d\n", line, ctonefreq);
      }
    } else if (tmp == strstr(tmp, "unlimitedrepeat=")) {
      unlimitedrepeat = 0;
      if (tmp[16] == '1')
        unlimitedrepeat = 1;
      printw("  line  %2d: unlimited repeat: %s\n", line, (unlimitedrepeat ? "yes" : "no"));
    } else if (tmp == strstr(tmp, "fixspeed=")) {
      fixspeed = 0;
      if (tmp[9] == '1')
        fixspeed = 1;
      printw("  line  %2d: fixed speed:  %s\n", line, (fixspeed ? "yes" : "no"));
    } else if (tmp == strstr(tmp, "unlimitedattempt=")) {
      unlimitedattempt = 0;
      if (tmp[17] == '1')
        unlimitedattempt = 1;
      printw("  line  %2d: unlimited attempts:  %s\n", line, (unlimitedattempt ? "yes" : "no"));
    } else if (tmp == strstr(tmp, "cbptr=")) {
      while (tmp[6 + i]) {
        tmp[i] = tmp[6 + i];
        i++;
      }
      tmp[i] = '\0';
      cbptr = atoi(tmp);
    } else if (tmp == strstr(tmp, "callbase=")) {
      while (tmp[9 + i]) {
        tmp[i] = tmp[9 + i];
        i++;
      }
      tmp[i] = '\0';
      // populate cblist
      if (strlen(tmp) > 1) {
        strcpy(cblist[cbindex++], tmp);
      } else {
        printw("  line  %2d: invalid path: %s\n", line, tmp);
        exit(0);
      }
    } else if (tmp == strstr(tmp, "samplerate=")) {
      while (isdigit(tmp[i] = tmp[11 + i]))
        i++;
      tmp[i] = '\0';
      samplerate = atoi(tmp);
      printw("  line  %2d: sample rate: %d\n", line, samplerate);
    }
    strcpy(cbfilename, cblist[cbptr]);
  }
  return 0;
}


static void *morse(void *arg)
{
  char *text = arg;
  int i, j;
  int c, fulldotlen, dotlen, dashlen, charspeed, farnsworth, fwdotlen;
  const char *code;

  // opening the DSP device
  dsp_fd = open_dsp(dspdevice);

  // set bufpos to 0
  full_bufpos = 0;

  // Some silence; otherwise the call starts right after pressing enter
  tonegen(0, samplerate / 4, SILENCE);

  // Farnsworth?
  if (speed < mincharspeed) {
    charspeed = mincharspeed;
    farnsworth = 1;
    fwdotlen = (int)(samplerate * 6 / speed);
  } else {
    charspeed = speed;
    farnsworth = 0;
  }

  // speed is in LpM now, so we have to calculate the dot-length in
  // milliseconds using the well-known formula  dotlength= 60/(wpm*50)
  // and then to samples

  dotlen = (int)(samplerate * 6 / charspeed);
  fulldotlen = dotlen;
  dashlen = 3 * dotlen;

  // edge = length of rise/fall time in ms. ed = in samples

  ed = (int)(samplerate * (edge / 1000.0));

  // the signal needs "ed" samples to reach the full amplitude and
  // at the end another "ed" samples to reach zero. The dots and
  // dashes therefore are becoming longer by "ed" and the pauses
  // after them are shortened accordingly by "ed" samples

  for (i = 0; i < strlen(text); i++) {
    c = text[i];
    if (isalpha(c))
      code = codetable[c - 65];
    else if (isdigit(c))
      code = codetable[c - 22];
    else if (c == '/')
      code = "-..-.";
    else if (c == '+')
      code = ".-.-.";
    else
      code = "..--..";     // not supposed to happen!

    // code is now available as string with - and .

    for (j = 0; j < strlen(code); j++) {
      c = code[j];
      if (c == '.') {
        tonegen(freq, dotlen + ed, waveform);
        tonegen(0, fulldotlen - ed, SILENCE);
      } else {
        tonegen(freq, dashlen + ed, waveform);
        tonegen(0, fulldotlen - ed, SILENCE);
      }
    }
    if (farnsworth)
      tonegen(0, 3 * fwdotlen - fulldotlen, SILENCE);
    else
      tonegen(0, 2 * fulldotlen, SILENCE);
  }

  write_audio(dsp_fd, &full_buf[0], full_bufpos);
  close_audio(dsp_fd);
  sending_complete = 1;
  starttime = get_ms();
  return NULL;
}

static int add_to_buf(void *data, int size) {
  memcpy(&full_buf[full_bufpos / sizeof(int)], data, size);
  full_bufpos += size;
  return 0;
}

// generate a sine tone of frequency and length
static int tonegen(int freq, int len, int waveform) {
  int x = 0;
  int out;
  double val = 0;

  for (x = 0; x < len - 1; x++) {
    switch (waveform) {
    case SINE:
      val = sin(2 * PI * freq * x / samplerate);
      break;
    case SAWTOOTH:
      val = ((1.0 * freq * x / samplerate) - floor(1.0 * freq * x / samplerate)) - 0.5;
      break;
    case SQUARE:
      val = ceil(sin(2 * PI * freq * x / samplerate)) - 0.5;
      break;
    case SILENCE:
      val = 0;
    }

    if (x < ed) val *= pow(sin(PI * x / (2.0 * ed)), 2);    // rising edge

    if (x > (len - ed))                                     // falling edge
      val *= pow(sin(2 * PI * (x - (len - ed) + ed) / (4 * ed)), 2);

    out = (int)(val * 32500.0);
    add_to_buf(&out, sizeof(out));
  }
  return 0;
}

static void thread_fail(int j) {
  if (j) {
    endwin();
    perror("Error: Unable to create cwthread!\n");
    exit(EXIT_FAILURE);
  }
}

// See where our files are. We need qrqrc and toplist
// The can be:
// 1) In the current directory
// 2) In ~/qrq/
// 3) In DESTDIR/share/qrq/ -> create ~/qrq and copy files
// 4) Nowhere --> Exit
static int find_files() {
  FILE *fh;
  const char *homedir = NULL;
  char tmp_rcfilename[1024] = "";
  char tmp_tlfilename[1024] = "";
  char tmp_cbfilename[1024] = "";

  printw("\nChecking for qrqrc and toplist files\n");

  if (((fh = fopen("qrqrc", "r")) == NULL) ||
      ((fh = fopen("toplist", "r")) == NULL)) {
    if ((homedir = getenv("HOME")) != NULL) {
      printw("... not found in current directory. Checking "
             "%s/qrq/...\n", homedir);
      refresh();
      strcat(rcfilename, homedir);
    } else {
      printw("... not found in current directory. Checking "
             "./qrq/...\n", homedir);
      refresh();
      strcat(rcfilename, ".");
    }

    strcat(rcfilename, "/qrq/qrqrc");

    // check if there is ~/qrq/qrqrc
    if ((fh = fopen(rcfilename, "r")) == NULL) {
      printw("... not found in %s/qrq/. Checking %s/share/qrq..."
             "\n", homedir, destdir);
      // check for the files in DESTDIR/share/qrq/. if exists, copy
      // qrqrc and toplist to ~/qrq/

      strcpy(tmp_rcfilename, destdir);
      strcat(tmp_rcfilename, "/share/qrq/qrqrc");
      strcpy(tmp_tlfilename, destdir);
      strcat(tmp_tlfilename, "/share/qrq/toplist");

      if (((fh = fopen(tmp_rcfilename, "r")) == NULL) ||
          ((fh = fopen(tmp_tlfilename, "r")) == NULL) ||
          ((fh = fopen(tmp_cbfilename, "r")) == NULL)) {
        printw("Could not find qrqrc and toplist.. Exiting..\n");
        getch();
        endwin();
        exit(EXIT_FAILURE);
      } else {
        // finally found it in DESTDIR/share/qrq/ !
        // abusing rcfilename here for something else temporarily
        printw("Found files in %s/share/qrq/."
               "\nCreating directory %s/qrq/ and copy qrqrc and"
               " toplist there.\n", destdir, homedir);
        strcpy(rcfilename, homedir);
        strcat(rcfilename, "/qrq/");
        j = mkdir(rcfilename, 0777);

        if (j && (errno != EEXIST)) {
          printw("Failed to create %s! Exit.\n", rcfilename);
          getch();
          endwin();
          exit(EXIT_FAILURE);
        }
        // now we created the directory, we can read in
        // DESTDIR/local/, so I assume copying files won't cause any
        // problem, with system()...

        strcpy(rcfilename, "install -m 644 ");
        strcat(rcfilename, tmp_tlfilename);
        strcat(rcfilename, " ");
        strcat(rcfilename, homedir);
        strcat(rcfilename, "/qrq/ 2> /dev/null");
        if (system(rcfilename)) {
          printw("Failed to copy toplist file: %s\n", rcfilename);
          getch();
          endwin();
          exit(EXIT_FAILURE);
        }
        strcpy(rcfilename, "install -m 644 ");
        strcat(rcfilename, tmp_rcfilename);
        strcat(rcfilename, " ");
        strcat(rcfilename, homedir);
        strcat(rcfilename, "/qrq/ 2> /dev/null");
        if (system(rcfilename)) {
          printw("Failed to copy qrqrc file: %s\n", rcfilename);
          getch();
          endwin();
          exit(EXIT_FAILURE);
        }
        printw("Files copied. You might want to edit "
               "qrqrc according to your needs.\n", homedir);
        strcpy(rcfilename, homedir);
        strcat(rcfilename, "/qrq/qrqrc");
        strcpy(tlfilename, homedir);
        strcat(tlfilename, "/qrq/toplist");
        strcpy(cbfilename, tmp_cbfilename);
      }       // found in DESTDIR/share/qrq/
    } else {
      printw("... found files in %s/qrq\n", homedir);
      strcat(tlfilename, homedir);
      strcat(tlfilename, "/qrq/toplist");
    }
  } else {
    printw("... found in current directory\n");
    strcpy(rcfilename, "qrqrc");
    strcpy(tlfilename, "toplist");
  }
  refresh();
  fclose(fh);
  return 0;
}


static int statistics() {
  char line[80] = "";
  int time = 0;
  int score = 0;
  int count = 0;
  FILE *fh;
  FILE *fh2;

  if ((fh = fopen(tlfilename, "r")) == NULL) {
    fprintf(stderr, "Unable to open toplist.");
    exit(0);
  }

  if ((fh2 = fopen("/tmp/qrq-plot", "w+")) == NULL) {
    fprintf(stderr, "Unable to open /tmp/qrq-plot.");
    exit(0);
  }

  fprintf(fh2, "set yrange [0:]\nset xlabel \"Date/Time\"\n"
          "set title \"QRQ scores for %s. Press 'q' to "
          "close this window.\"\n"
          "set ylabel \"Score\"\nset xdata time\nset "
          " timefmt \"%%s\"\n "
          "plot \"-\" using 1:2 title \"\"\n", mycall);

  while ((feof(fh) == 0) && (fgets(line, 80, fh) != NULL)) {
    if ((strstr(line, mycall) != NULL)) {
      count++;
      sscanf(line, "%*s %d %*d %d", &score, &time);
      fprintf(fh2, "%d %d\n", time, score);
    }
  }

  if (!count) fprintf(fh2, "0 0\n");

  fprintf(fh2, "end\npause 10000");
  fclose(fh);
  fclose(fh2);

  system("gnuplot /tmp/qrq-plot 2> /dev/null &");
  return 0;
}


int read_callbase() {
  FILE *fh;
  int c, i;
  int maxlen = 0;
  char tmp[80] = "";
  int nr = 0;

  if ((fh = fopen(cbfilename, "r")) == NULL) {
    endwin();
    fprintf(stderr, "Error: Couldn't read callsign database ('%s')!\n",
            cbfilename);
    exit(EXIT_FAILURE);
  }

  // count the lines/calls and lengths
  i = 0;
  while ((c = getc(fh)) != EOF) {
    i++;
    if (c == '\n') {
      nr++;
      maxlen = (i > maxlen) ? i : maxlen;
      i = 0;
    }
  }
  maxlen++;

  if (!nr) {
    endwin();
    printf("\nError: %s is empty\n", cbfilename);
    exit(EXIT_FAILURE);
  }

  // allocate memory for calls array, free if needed
  free(calls);

  if ((calls = (char **)malloc((size_t)sizeof(char *) * nr)) == NULL) {
    fprintf(stderr, "Error: Couldn't allocate %d bytes!\n",
            (int)sizeof(char) * nr);
    exit(EXIT_FAILURE);
  }

  // Allocate each element of the array with size maxlen
  for (c = 0; c < nr; c++) {
    if ((calls[c] = (char *)malloc(maxlen * sizeof(char))) == NULL) {
      fprintf(stderr, "Error: Couldn't allocate %d bytes!\n", maxlen);
      exit(EXIT_FAILURE);
    }
  }

  rewind(fh);

  nr = 0;
  while (fgets(tmp, maxlen, fh) != NULL) {
    for (i = 0; i < strlen(tmp); i++)
      tmp[i] = toupper(tmp[i]);
    tmp[i - 1] = '\0';              // remove newline
    if (tmp[i - 2] == '\r')         // also for DOS files
      tmp[i - 2] = '\0';
    strcpy(calls[nr], tmp);
    nr++;
    if (nr == c)                    // may happen if call file corrupted
      break;
  }
  fclose(fh);


  return nr;
}

void select_callbase() {
  int i = 0, j = 0, k = 0;
  int c = 0;        // cursor position  
  int p = 0;        // page a 10 entries
  char *cblist_ptr;

  curs_set(FALSE);

  // count files
  while (strcmp(cblist[i], "")) i++;

  if (!i) {
    mvwprintw(conf_w, 10, 4, "No callbase files found!");
    wrefresh(conf_w);
    sleep(1);
    return;
  }

  // loop for key unput
  while (1) {
    // cls
    for (j = 5; j < 16; j++)
      mvwprintw(conf_w, j, 2, "                                         ");

    // display 10 files, highlight cursor position
    for (j = p * 10; j < (p + 1) * 10; j++) {
      if (j <= i) {
        cblist_ptr = cblist[j];
        mvwprintw(conf_w, 3 + (j - p * 10), 2, "  %s       ", cblist_ptr);
      }
      if (c == j)                           // cursor
        mvwprintw(conf_w, 3 + (j - p * 10), 2, ">");
    }

    wrefresh(conf_w);
    k = getch();

    switch ((int)k) {
    case KEY_UP:
      c = (c > 0) ? (c - 1) : c;
      if (!((c + 1) % 10))          // scroll down
        p = (p > 0) ? (p - 1) : p;
      break;
    case KEY_DOWN:
      c = (c < i - 1) ? (c + 1) : c;
      if (c && !(c % 10))           // scroll down
        p++;
      break;
    case '\n':
      strcpy(cbfilename, cblist[c]);
      cbptr = c;                    // callbase pointer
      nrofcalls = read_callbase();
      return;
      break;
    }
    wrefresh(conf_w);
  }
  curs_set(TRUE);
}

long long get_ms() {
  struct timeval te; 
  gettimeofday(&te, NULL);
  long long ms = te.tv_sec*1000LL + te.tv_usec/1000;
  return ms;
}

void help() {
  printf("qrq v%s  (c) 2006-2013 Fabian Kurz, DJ1YFK. "
         "http://fkurz.net/ham/qrq.html\n", VERSION);
  printf("High speed morse telegraphy trainer, similar to RUFZ.\n\n");
  printf("This is free software, and you are welcome to redistribute it\n");
  printf("under certain conditions (see COPYING).\n\n");
  printf("Start 'qrq' with no command line args for normal operation.\n");
  exit(0);
}

