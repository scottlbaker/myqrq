
// Copyright (c) 2011  Fabian Kurz, DJ1YFK
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

#include <ncurses.h>
#include <stdlib.h>
#include <fcntl.h>
#include <pulse/simple.h>
#include <pulse/error.h>

extern long samplerate;
extern void *dsp_fd;

short int buf[441000];      // 10 second buffer
int bufpos = 0;

void *open_dsp() {
  static int opened = 0;

  // open the device and leave it open
  if (opened) return dsp_fd;

  // sample format
  static pa_sample_spec ss = {
    .format    = PA_SAMPLE_S16LE,
    .rate      = 8000,
    .channels  = 1
  };
  ss.rate = samplerate;
  pa_simple *s = NULL;
  int error;

  if (!(s = pa_simple_new(NULL, "qrq", PA_STREAM_PLAYBACK, NULL,
                          "playback", &ss, NULL, NULL, &error)))
    fprintf(stderr, "pa_simple_new() failed: %s\n",
            pa_strerror(error));

  opened = 1;
  return s;
}

// write sample into the buffer
void write_audio(void *bla, int *in, int size) {
  int i = 0;
  for (i = 0; i < size / sizeof(int); i++) {
    buf[bufpos] = (short int)in[i];
    bufpos++;
  }
}

// close audio
void close_audio(void *s) {
  int e;
  pa_simple_write(s, buf, bufpos * sizeof(short int), &e);
  pa_simple_drain(s, &e);
  bufpos = 0;
}
