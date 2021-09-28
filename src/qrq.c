
// qrq - High speed morse trainer, similar to the DOS classic "Rufz"
// original Copyright (c) 2006-2013  Fabian Kurz
// modifications Copyright (c) 2021  Scott L. Baker
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

#define MYFREQ   700     // default tone frequency
#define MAXFREQ  800     // max tone frequency
#define MINFREQ  400     // min tone frequency

#define VERSION  "0.3.1x"

#ifndef DESTDIR
#   define DESTDIR "/usr"
#endif

#include "pulseaudio.h"
typedef void *AUDIO_HANDLE;

// call array
static char calls[5000][10];

const static char *codetable[] = {
  ".-",    "-...", "-.-.",  "-..",  ".",   "..-.",  "--.", "....",  "..",   ".---",
  "-.-",   ".-..", "--",  "-.",  "---",   ".--.",  "--.-", ".-.",  "...",   "-",   "..-","...-",
  ".--",   "-..-", "-.--",  "--..", "-----", ".----", "..---", "...--", "....-", ".....",
  "-....", "--...", "---..", "----."
};

static char cblist[100][PATH_MAX];              // List of available callbase files
static char mycall[15] = "DJ1YFK";              // user callsign read from qrqrc
static char dspdevice[PATH_MAX] = "/dev/dsp";   // DSP device is read from qrqrc

static int cbtot   = 0;                         // total callbase entries
static int cbptr   = 0;                         // callbase pointer
static int page    = 0;                         // callbase display page
static int maxpage = 0;                         // max callbase display page
static int crpos   = 0;                         // cursor position
static int score = 0;                           // session score
static int sending_complete;                    // global lock for "enter" while sending
static int singlechar;                          // for single character practice
static int callnr = 0;                          // nr of actual call in attempt
static int initialspeed = 200;                  // initial speed. to be read from file
static int mincharspeed = 0;                    // min. char. speed, below: farnsworth
static int speed = 200;                         // current speed in cpm
static int maxspeed = 0;
static int errornr = 0;                         // number of errors in attempt
static int p = 0;                               // position of cursor, relative to x
static int status = 1;                          // 1= attempt, 2=config
static int mode = 1;                            // 0 = overwrite, 1 = insert
static int j = 0;                               // counter etc.
static int fixedtone = 1;                       // if 1 don't change the pitch
static int ctonefreq = MYFREQ;                  // if fixedtone=1 use this freq
static int freq = MYFREQ;                       // current cw sidetone freq
static int unlimitedrepeat = 0;                 // allow unlimited repeats
static int fixspeed = 0;                        // keep speed fixed, regardless of err
static int mstime = 0;                          // millisecond timer

static unsigned long int nrofcalls = 0;
static long long starttime = 0;
static long long endtime = 0;

long samplerate = 44100;
static long long_i;
static int waveform = SINE;             // waveform: (0 = none)
static char wavename[10] = "Sine    ";  // Name of the waveform
static double edge = 2.0;               // rise/fall time in milliseconds
static int ed;                          // risetime, normalized to samplerate
static short buffer[88200];
static int full_buf[882000];            // 20 second max buffer
static int full_bufpos = 0;

#define NTONE 4
static int ctonelist[NTONE] = {550,600,650,700};

AUDIO_HANDLE dsp_fd;

static int  display_toplist();
static int  calc_score(char *realcall, char *input, int speed, char *output);
static int  update_score();
static int  show_error(char *realcall, char *wrongcall);
static int  clear_display();
static int  read_config();
static int  tonegen(int freq, int length, int waveform);
static void *morse(void *arg);
static int  add_to_buf(void *data, int size);
static int  readline(WINDOW *win, int y, int x, char *line, int i);
static void check_thread(int j);
static int  find_files();
static int  statistics();
static int  read_callbase();
static void select_callbase();
static void check_tone();
static void exit_program();
static long long get_ms();
static void help();
static void callbase_dialog();
static void parameter_dialog();
static int  clear_parameter_display();
static void update_parameter_dialog();

pthread_t cwthread;            // thread for CW output, to enable
pthread_attr_t cwattr;         // keyboard reading at the same time

char rcfilename[PATH_MAX] = "";  // filename and path to qrqrc
char tlfilename[PATH_MAX] = "";  // filename and path to toplist
char cbfilename[PATH_MAX] = "";  // filename and path to callbase

char destdir[PATH_MAX] = "";

// create windows
WINDOW *top_w;                  // actual score
WINDOW *mid_w;                  // call history/mistakes
WINDOW *conf_w;                 // parameter config display
WINDOW *bot_w;                  // user input line
WINDOW *inf_w;                  // info window for param displ
WINDOW *right_w;                // highscore list/settings


int main(int argc, char *argv[]) {
  strcpy(destdir, DESTDIR);
  char tmp[80] = "";
  char input[15] = "";
  int i = 0, j = 0, k = 0;
  char previouscall[80] = "";
  int previousfreq = 0;

  if (argc > 1)
    help();

  (void)initscr();
  cbreak();
  noecho();
  curs_set(FALSE);
  keypad(stdscr, TRUE);
  scrollok(stdscr, FALSE);

  printw("\nqrq v%s   A high-speed morse trainer    \n", VERSION);
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

  // read the call database
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
  j = pthread_create(&cwthread, NULL, &morse, (void *)"");
  check_thread(j);

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
      mvwprintw(top_w, 1, 1, "qrq v%s", VERSION);
      wattroff(top_w, A_BOLD);
      mvwaddstr(top_w, 1, 12, " :: A high-speed morse code trainer       ");
      mvwaddstr(top_w, 2, 1,  "                                          ");
      clear_display();
      wattron(mid_w, A_BOLD);
      mvwaddstr(mid_w, 1, 1,  "Usage:");
      wattroff(mid_w, A_BOLD);
      mvwaddstr(mid_w,  3, 2, "After entering your callsign, random calls         ");
      mvwaddstr(mid_w,  4, 2, "from a database will be sent. After each call,     ");
      mvwaddstr(mid_w,  5, 2, "enter what you have heard. If you copied correctly,");
      mvwaddstr(mid_w,  6, 2, "then points are credited.                          ");
      mvwaddstr(mid_w,  9, 2, "Press F7 to repeat the previous call               ");
      mvwaddstr(mid_w, 10, 2, "Press F6 or F1 to repeat the current call          ");
      mvwaddstr(mid_w, 11, 2, "Press F5 to change settings                        ");
      mvwaddstr(mid_w, 12, 2, "Press F4 to quit                                   ");

      wattron(right_w, A_BOLD);
      mvwaddstr(right_w, 1, 6, "Toplist");
      wattroff(right_w, A_BOLD);
      display_toplist();
      p = 0;                    // cursor to start position
      wattron(bot_w, A_BOLD);
      mvwaddstr(bot_w, 1, 1,  "Please enter your callsign                         ");
      wattroff(bot_w, A_BOLD);
      wrefresh(top_w);
      wrefresh(mid_w);
      wrefresh(bot_w);
      wrefresh(right_w);
      maxspeed = errornr = score = 0;
      speed = initialspeed;

      // prompt for own callsign
      i = readline(bot_w, 1, 30, mycall, 1);

      // F4 -> quit
      if (i == 4) {
        exit_program();
      }
      // F5 -> configuration
      if (i == 5) {
        parameter_dialog();
        break;
      }
      // F6 -> play test CW
      else if (i == 6) {
        pthread_join(cwthread, NULL);
        j = pthread_create(&cwthread, NULL, &morse, (void *)"VVVTEST");
        check_thread(j);
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

      // update toplist
      display_toplist();
      mvwprintw(top_w, 1, 1, "                                            ");
      mvwprintw(top_w, 2, 1, "                                            ");
      wattron(top_w, A_BOLD);
      mvwprintw(top_w, 1, 1, "%s", mycall);
      wattroff(top_w, A_BOLD);
      update_score();
      wrefresh(top_w);

      // re-read the callbase
      nrofcalls = read_callbase();

      for (callnr = 1; callnr < nrofcalls; callnr++) {
        // wait for the cwthread of the previous call
        pthread_join(cwthread, NULL);
        // select an unused call from the calls array
        do i = rand() % (nrofcalls - 1);
        while (calls[i][0] == '\0');

        // only relevant for callbases with less than 50 calls
        if (nrofcalls == callnr)        // Only one call left!"
          callnr = 51;                  // Get out after next one

        // select CW tone
        if (fixedtone)
          freq = ctonefreq;
        else
          freq = ctonelist[rand() % (NTONE)];

        mvwprintw(bot_w, 1, 1, "                                      ");
        mvwprintw(bot_w, 1, 1, "%d/%d", callnr, nrofcalls-1);
        wrefresh(bot_w);
        tmp[0] = '\0';

        // starting the morse output in a separate process to make
        // keyboard input and echoing at the same time possible
        sending_complete = 0;
        j = pthread_create(&cwthread, NULL, morse, calls[i]);
        check_thread(j);

        // check for function key press
        while ((j = readline(bot_w, 1, 8, input, 1)) > 1) {
          switch (j) {
          case 4:              // F4 -> quit program
            exit_program();
            break;
          case 6:              // F6 -> repeat current call
            // wait for old cwthread to finish, then send call again
            pthread_join(cwthread, NULL);
            j = pthread_create(&cwthread, NULL, &morse, calls[i]);
            check_thread(j);
            break;
          case 7:              // F7 -> repeat previous call
            if (callnr > 1) {
              k = freq;
              freq = previousfreq;
              pthread_join(cwthread, NULL);
              j = pthread_create(&cwthread, NULL, &morse, previouscall);
              check_thread(j);
              // wait for the CW thread before restore freq
              // this blocks keyboard input
              pthread_join(cwthread, NULL);
              freq = k;
            }
            break;
          default:
            break;
          }
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
        calls[i][0] = '\0';
      }

      // attempt is over
      callnr = 0;
      i = nrofcalls-1;
      pthread_join(cwthread, NULL);  // wait for cwthread to finish
      curs_set(0);
      wattron(bot_w, A_BOLD);
      mvwprintw(bot_w, 1, 1, "%d/%d completed.. Press any key to continue!", i,i);
      wattroff(bot_w, A_BOLD);
      wrefresh(bot_w);

      j = pthread_create(&cwthread, NULL, &morse, (void *)"EE");
      check_thread(j);
      pthread_join(cwthread, NULL);  // wait for cwthread to finish
      
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

  #define KEY_RETN 10

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
    case 'k':                               // fixed or variable CW tone
      ctonefreq -= 10;
      check_tone();
      break;
    case 'l':
      ctonefreq += 10;
      check_tone();
      break;
    case '0':
      if (fixedtone == 1)
        fixedtone = 0;
      else
        fixedtone = 1;
      break;
    case 'f':
      unlimitedrepeat = (unlimitedrepeat ? 0 : 1);
      break;
    case 's':
      fixspeed = (fixspeed ? 0 : 1);
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
      pthread_join(cwthread, NULL);
      j = pthread_create(&cwthread, NULL, &morse, (void *)"TESTING");
      check_thread(j);
      break;
    case KEY_RETN:   // ENTER KEY
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
            "                 k/l or 0", (fixedtone) ? ctonefreq : 0);
  mvwprintw(conf_w, 7, 2, "CW waveform:           %-8s"
            "             w", wavename);
  mvwprintw(conf_w, 8, 2, "Unlimited repeat:      %-3s"
            "                  f", (unlimitedrepeat ? "yes" : "no"));
  mvwprintw(conf_w, 9, 2, "Fixed CW speed:        %-3s"
            "                  s", (fixspeed ? "yes" : "no"));
  mvwprintw(conf_w, 11, 2, "callbase:  %-15s"
            "   d (%d)", basename(cbfilename), nrofcalls-1);

  mvwprintw(conf_w, 14, 2, "Press Enter to continue");
  wrefresh(conf_w);
  wrefresh(inf_w);
}


void callbase_dialog() {
  clear_parameter_display();
  wattron(conf_w, A_BOLD);
  mvwaddstr(conf_w, 1, 1, "Change Call Database");
  wattroff(conf_w, A_BOLD);
  select_callbase();
  wrefresh(conf_w);
  return;
}


// read call data
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
    // exit loop if user hits the enter key
    if ((c == '\n') && sending_complete) break;

    if (((c >= 'a' && c <= 'z') ||
         (c >= 'A' && c <= 'Z') ||
         (c >= '0' && c <= '9') ||
         (c == '/') || (c == '=') ||
         (c == '.') || (c == ',') ||
         (c == '#') || (c == '!') ||
         (c == ';') || (c == '-') ||
         (c == '+') || (c == '?')) && (strlen(line) < 14)) {

      // for single character practice
      if (singlechar) {
        line[p] = toupper(c);
        line[strlen(line) + 1] = '\0';
        break;
      }

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
    } else if (c == KEY_IC) {                  // INS/OVR
      if (mode == 1) {
        mode = 0;
        mvwaddstr(win, 1, 55, "OVR");
      } else {
        mode = 1;
        mvwaddstr(win, 1, 55, "INS");
      }
    } else if (c == KEY_F(4)) {                // F4 -> quit
      return 4;
    } else if (c == KEY_F(5)) {                // F5 -> settings
      parameter_dialog();
    // alias multiple keys                     // F6 (repeat call)
    } else if ((c == KEY_LEFT)  || (c == KEY_RIGHT) ||
               (c == KEY_DOWN)  || (c == KEY_UP)    ||
               (c == KEY_PPAGE) || (c == KEY_NPAGE) ||
               (c == KEY_HOME)  || (c == KEY_END)   ||
               (c == KEY_DC)    || (c == KEY_F(1))  ||
               (c == KEY_F(2))  || (c == KEY_F(3))  ||
               (c == KEY_F(6))) {
      return 6;
    } else if (c == KEY_F(7)) {
      return 7;
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
  int i, lngth, mistake = 0;

  lngth = strlen(realcall);

  if (strcmp(input, realcall) == 0) {       // exact match!
    output[0] = '*';                        // * == OK, no mistake
    output[1] = '\0';
    if (speed > maxspeed) maxspeed = speed;
    if (!fixspeed) speed += 10;
    return (int)(2 * lngth * spd);          // score
  } else {                                  // assemble error string
    errornr += 1;
    if (strlen(input) >= lngth) lngth = strlen(input);
    for (i = 0; i < lngth; i++) {
      if (realcall[i] != input[i]) {
        mistake++;                          // mistake!
        output[i] = tolower(input[i]);      // print as lower case
      } else {
        output[i] = input[i];
      }
    }
    output[i] = '\0';
    // slow down if not in fixed speed mode
    if ((speed > 29) && !fixspeed) speed -= 10;
    return 0; ;
  }
}

// print score, current speed and max speed to window
static int update_score() {
  mvwaddstr(top_w, 1, 10, "Score:                                   ");
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

// Display the correct call and what the user entered
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

    // find user callsign, speed etc.
    // only allow if the lines are beginning at zero
    if (tmp == strstr(tmp, "callsign=")) {
      while (isalnum(tmp[i] = toupper(tmp[9 + i])))
        i++;
      tmp[i] = '\0';
      if (strlen(tmp) < 8) {            // empty call allowed
        strcpy(mycall, tmp);
        printw("  line  %2d: call: %s\n", line, mycall);
      } else {
        printw("  line  %2d: call: %s too long. "
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
    } else if (tmp == strstr(tmp, "fixedtone=")) {
      while (isdigit(tmp[i] = tmp[13 + i]))
        i++;
      tmp[i] = '\0';
      k = 0;
      k = atoi(tmp);
      if ((k * k) > 1) {
        printw("  line  %2d: constant tone: %s invalid. "
               "Using default %d.\n", line, tmp, fixedtone);
      } else {
        fixedtone = k;
        printw("  line  %2d: constant tone: %d\n", line, fixedtone);
      }
    } else if (tmp == strstr(tmp, "ctonefreq=")) {
      while (isdigit(tmp[i] = tmp[10 + i]))
        i++;
      tmp[i] = '\0';
      k = atoi(tmp);
      if ((k > MAXFREQ) || (k < MINFREQ)) {
        printw("  line  %2d: ctonefreq: %s invalid. "
               "Using default %d.\n", line, tmp, ctonefreq);
        ctonefreq = MYFREQ;
      } else {
        ctonefreq = k;
        printw("  line  %2d: CW tone (Hz): %d\n", line, ctonefreq);
      }
      freq = ctonefreq;
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
        strcpy(cblist[cbtot++], tmp);
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

  if (!cbtot) {
    printw("  No callbase files found!");
    exit(0);
  }
  maxpage = (int)(cbtot/10);
  return 0;
}


static void *morse(void *arg) {
  char *text = arg;
  int i, j;
  int c, fulldotlen, dotlen, dashlen, charspeed, farnsworth, fwdotlen;
  const char *code;

  // opening the DSP device
  dsp_fd = open_dsp(dspdevice);

  // set bufpos to 0
  full_bufpos = 0;

  // some silence
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
    else if (c == '=')
      code = "-...-";
    else if (c == '.')
      code = ".-.-.-";
    else if (c == '!')
      code = "-.-.--";
    else if (c == ',')
      code = "--..--";
    else if (c == ';')
      code = "-.-.-.";
    else if (c == '#')
      code = "-.-.-";
    else if (c == '+')
      code = ".-.-.";
    else if (c == '-')
      code = "-....-";
    else
      code = "..--..";     // ?

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

// verify that thread was created OK
static void check_thread(int j) {
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
    fprintf(stderr, "Error: Couldn't read call database ('%s')!\n",
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
  // for single character practice
  if (maxlen == 3) singlechar = 1;
  else singlechar = 0;

  if (!nr) {
    endwin();
    printf("\nError: %s is empty\n", cbfilename);
    exit(EXIT_FAILURE);
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
  }
  fclose(fh);
  return nr+1;
}

void select_callbase() {
  int cbidx = 0, key = 0;

  curs_set(FALSE);

  // loop for key input
  while (1) {
    // clear file names from screen
    for (cbidx = 4; cbidx < 16; cbidx++)
      mvwprintw(conf_w, cbidx, 2, "                                              ");

    // then display 10 file names with cursor mark
    for (cbidx = page * 10; cbidx < (page + 1) * 10; cbidx++) {
      if (cbidx < cbtot) {
        mvwprintw(conf_w, 3 + (cbidx - (page * 10)), 2, "  %s ", basename(cblist[cbidx]));
      }
      if (cbidx == crpos)
        mvwprintw(conf_w, 3 + (cbidx - (page * 10)), 2, ">");
    }

    wrefresh(conf_w);
    key = (int)getch();

    switch (key) {
    case KEY_UP:
      crpos = (crpos > 0) ? (crpos - 1) : crpos;
      if (!((crpos + 1) % 10))          // scroll down
        page = (page > 0) ? (page - 1) : page;
      break;
    case KEY_DOWN:
      crpos = (crpos < cbtot - 1) ? (crpos + 1) : crpos;
      if (crpos && !(crpos % 10))       // scroll down
        page = (page < maxpage) ? (page + 1) : page;
      break;
    case '\n':
      strcpy(cbfilename, cblist[crpos]);
      cbptr = crpos;                    // callbase pointer
      nrofcalls = read_callbase();
      return;
      break;
    }
    wrefresh(conf_w);
  }
  curs_set(TRUE);
}


void check_tone() {
  if (ctonefreq > MAXFREQ) ctonefreq = MAXFREQ;
  if (ctonefreq < MINFREQ) ctonefreq = MINFREQ;
}


void exit_program() {
  // wait for the cw thread
  pthread_join(cwthread, NULL);
  // send 73
  j = pthread_create(&cwthread, NULL, &morse, (void *)"73");
  check_thread(j);
  // wait for the cw thread
  pthread_join(cwthread, NULL);
  endwin();
  printf("\nThank You for using qrq version %s !!\n\n", VERSION);
  exit(0);
}


long long get_ms() {
  struct timeval te; 
  gettimeofday(&te, NULL);
  long long ms = te.tv_sec*1000LL + te.tv_usec/1000;
  return ms;
}


void help() {
  printf("\n");
  printf("qrq (c) 2006-2013 Fabian Kurz, DJ1YFK\n");
  printf("High speed morse code trainer\n");
  printf("This is free software, and you are welcome to\n");
  printf("redistribute it under certain conditions (see COPYING)\n");
  printf("Start 'qrq' with no command line args for normal operation\n");
  exit(0);
}

