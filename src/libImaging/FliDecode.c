/*
 * The Python Imaging Library.
 * $Id$
 *
 * decoder for Autodesk Animator FLI/FLC animations
 *
 * history:
 *	97-01-03 fl	Created
 *	97-01-17 fl	Added SS2 support (FLC)
 *
 * Copyright (c) Fredrik Lundh 1997.
 * Copyright (c) Secret Labs AB 1997.
 *
 * See the README file for information on usage and redistribution.
 */


#include "Imaging.h"


#define    I16(ptr)\
    ((ptr)[0] + ((ptr)[1] << 8))

/*@
  @ requires \valid(ptr + (0..1));
  @ ensures \result == (ptr[1] << 8) + (ptr[0]);
  @ ensures 0 <= \result <= 0xffff;
  @ assigns \nothing;
  @*/
int I16_fixed(UINT8 * ptr) {
    int result = 0;

    result += ptr[1];
    //@ assert 0 < result <= 0xff;
    result <<= 8;
    //@ assert 0 < result <= 0xff00;
    result += ptr[0];
    //@ assert 0 < result <= 0xffff;

    return result;
}

#define    I32(ptr)\
    ((ptr)[0] + ((ptr)[1] << 8) + ((ptr)[2] << 16) + ((ptr)[3] << 24))

/*@
  @ requires \valid(ptr + (0..3));
  @ ensures \result == (ptr[3] << 24) + (ptr[2] << 16) + (ptr[1] << 8) + (ptr[0]);
  @ ensures INT_MIN <= \result <= INT_MAX;
  @ assigns \nothing;
  @*/
int I32_fixed(UINT8 *ptr) {
    int result = 0;

    //@ assert 0 <= ptr[0] <= 0xff;
    int p0 = ptr[0];
    //@ assert 0 <= p0 <= 0xff;

    //@ assert 0 <= ptr[1] <= 0xff;
    int p1 = ptr[1];
    //@ assert 0 <= p1 <= 0xff;

    //@ assert 0 <= ptr[2] <= 0xff;
    int p2 = ptr[2];
    //@ assert 0 <= p2 <= 0xff;

    //@ assert 0 <= ptr[3] <= 0xff;
    int p3 = ptr[3];
    //@ assert 0 <= p3 <= 0xff;

    result += p3;
    //@ assert 0 <= result <= 0xff;
    result <<= 8;
    //@ assert 0 <= result <= 0xff00;
    result += p2;
    //@ assert 0 <= result <= 0xffff;
    result <<= 8;
    //@ assert 0 <= result <= 0xffff00;
    result += p1;
    //@ assert 0 <= result <= 0xffffff;
    result <<= 8;
    //@ assert 0xffffff00 <= result <= 0x80000000 || 0 <= result <= 0x7fffff00;
    result += p0;
    //@ assert INT_MIN <= result <= INT_MAX;

    return result;
}


#define BAIL_ON(condition) {if (condition) {return -1;}}

/*@
 requires 16 <= bytes && bytes <= 4096;
 requires (0 < state->ysize && 0 < state->xsize) || state->ysize == state->xsize == 0;
 requires state->ysize * state->xsize < 0x7fffffff - 32;
 requires \valid(buf + (0..bytes - 1));
 requires \valid(im);
 requires \valid(state);
 requires \valid(im->image + (0..state->ysize - 1));
 requires \forall integer y; 0 <= y < state->ysize ==> \valid(im->image[y] + (0..state->xsize - 1));
 requires \separated(buf + (0..bytes - 1), im->image + (0..state->ysize - 1));
 requires \forall integer y; 0 <= y < state->ysize ==> \separated(buf + (0..bytes - 1), im->image[y] + (0..state->xsize - 1));
 ensures bytes < 4 ==> \result == 0;
 ensures bytes >= 4 ==> \result == -1;
 ensures (buf[5] != 0xF1 || buf[4] != 0xFA) ==> \result == -1;
 */
int
ImagingFliDecode(Imaging im, ImagingCodecState state, UINT8 *buf, Py_ssize_t bytes) {
    UINT8 *ptr;
    int framesize;
    int c, chunks, advance;
    int l, lines;
    int i, j, x = 0, y, ymax;
    Py_ssize_t bytes_original;

    /* If not even the chunk size is present, we'd better leave */

    if (bytes < 4) {
        // Unreachable or bug
        return 0;
    }

    /* We don't decode anything unless we have a full chunk in the
       input buffer (on the other hand, the Python part of the driver
       makes sure this is always the case) */

    bytes_original = bytes;
    ptr = buf;

    //@ assert \valid(buf + (0..bytes - 1));
    //@ assert \valid(ptr + (0..bytes - 1));

    framesize = I32_fixed(ptr);
    if (framesize < I32_fixed(ptr)) {
        // Unreachable
        return 0;
    }

    /* Make sure this is a frame chunk.  The Python driver takes
       case of other chunk types. */

    if (I16_fixed(ptr + 4) != 0xF1FA) {
        state->errcode = IMAGING_CODEC_UNKNOWN;
        return -1;
    }

    chunks = I16_fixed(ptr + 6);
    ptr += 16;
    bytes -= 16;

    //@ assert ptr + bytes == buf + bytes_original;

    /* Process subchunks */
    /*@
      @ loop assigns ptr, bytes, im->image[0..state->ysize - 1][0..state->xsize - 1];
      @ loop invariant (\valid(ptr + (0..bytes - 1)));
      @ loop invariant ptr + bytes == buf + bytes_original;
      @ loop invariant \valid(im->image + (0..state->ysize - 1));
      @ loop invariant \forall integer y; 0 <= y < state->ysize ==> \valid(im->image[y] + (0..state->xsize - 1));
      @ loop invariant \separated(ptr + (0..bytes - 1), im->image + (0..state->ysize - 1));
      @ loop invariant \forall integer y; 0 <= y < state->ysize ==> \separated(ptr + (0..bytes - 1), im->image[y] + (0..state->xsize - 1));
      @*/
    for (c = 0; c < chunks; c++) {
        if (bytes < 10) {
            state->errcode = IMAGING_CODEC_OVERRUN;
            return -1;
        }
        UINT8 *data;
        data = ptr + 6;
        switch (I16_fixed(ptr + 4)) {
            case 4:
            case 11:
                /* FLI COLOR chunk */
                break; /* ignored; handled by Python code */
            case 7: BAIL_ON(1);
                /* FLI SS2 chunk (word delta) */
                lines = I16_fixed(data);
                data += 2;
                for (l = y = 0; l < lines && y < state->ysize; l++, y++) {
                    UINT8 *buf_alt = (UINT8 *) im->image[y];
                    int p, packets;
                    packets = I16_fixed(data);
                    data += 2;
                    while (packets & 0x8000) {
                        /* flag word */
                        if (packets & 0x4000) {
                            y += 65536 - packets; /* skip lines */
                            if (y >= state->ysize) {
                                state->errcode = IMAGING_CODEC_OVERRUN;
                                return -1;
                            }
                            buf_alt = (UINT8 *) im->image[y];
                        } else {
                            /* store last byte (used if line width is odd) */
                            buf_alt[state->xsize - 1] = (UINT8) packets;
                        }
                        packets = I16_fixed(data);
                        data += 2;
                    }
                    for (p = x = 0; p < packets; p++) {
                        x += data[0]; /* pixel skip */
                        if (data[1] >= 128) {
                            i = 256 - data[1]; /* run */
                            if (x + i + i > state->xsize)
                                break;
                            for (j = 0; j < i; j++) {
                                buf_alt[x++] = data[2];
                                buf_alt[x++] = data[3];
                            }
                            data += 2 + 2;
                        } else {
                            i = 2 * (int) data[1]; /* chunk */
                            if (x + i > state->xsize)
                                break;
                            memcpy(buf_alt + x, data + 2, i);
                            data += 2 + i;
                            x += i;
                        }
                    }
                    if (p < packets)
                        break; /* didn't process all packets */
                }
                if (l < lines) {
                    /* didn't process all lines */
                    state->errcode = IMAGING_CODEC_OVERRUN;
                    return -1;
                }
                break;
            case 12: BAIL_ON(1);
                /* FLI LC chunk (byte delta) */
                y = I16_fixed(data);
                ymax = y + I16_fixed(data + 2);
                data += 4;
                for (; y < ymax && y < state->ysize; y++) {
                    UINT8 *out = (UINT8 *) im->image[y];
                    int p, packets = *data++;
                    for (p = x = 0; p < packets; p++, x += i) {
                        x += data[0]; /* skip pixels */
                        if (data[1] & 0x80) {
                            i = 256 - data[1]; /* run */
                            if (x + i > state->xsize)
                                break;
                            memset(out + x, data[2], i);
                            data += 3;
                        } else {
                            i = data[1]; /* chunk */
                            if (x + i > state->xsize)
                                break;
                            memcpy(out + x, data + 2, i);
                            data += i + 2;
                        }
                    }
                    if (p < packets)
                        break; /* didn't process all packets */
                }
                if (y < ymax) {
                    /* didn't process all lines */
                    state->errcode = IMAGING_CODEC_OVERRUN;
                    return -1;
                }
                break;
            case 13: BAIL_ON(1);
                /* FLI BLACK chunk */
                for (y = 0; y < state->ysize; y++)
                    memset(im->image[y], 0, state->xsize);
                break;
            case 15: BAIL_ON(1);
                /* FLI BRUN chunk */
                for (y = 0; y < state->ysize; y++) {
                    UINT8 *out = (UINT8 *) im->image[y];
                    data += 1; /* ignore packetcount byte */
                    for (x = 0; x < state->xsize; x += i) {
                        if (data[0] & 0x80) {
                            i = 256 - data[0];
                            if (x + i > state->xsize)
                                break; /* safety first */
                            memcpy(out + x, data + 1, i);
                            data += i + 1;
                        } else {
                            i = data[0];
                            if (x + i > state->xsize)
                                break; /* safety first */
                            memset(out + x, data[1], i);
                            data += 2;
                        }
                    }
                    if (x != state->xsize) {
                        /* didn't unpack whole line */
                        state->errcode = IMAGING_CODEC_OVERRUN;
                        return -1;
                    }
                }
                break;
            case 16:
                /* COPY chunk */
            BAIL_ON(bytes < 6 + state->ysize * state->xsize);
//                  @ loop assigns y, im->image[0..state->ysize - 1][0..state->xsize - 1];
                /*@
                  @ loop invariant data == ptr + 6 + y * state->xsize;
                  @ loop invariant bytes >= 6 + state->ysize * state->xsize;
                  @ loop invariant ptr + bytes == buf + bytes_original;
                  @ loop invariant \valid(ptr + (0..bytes - 1));
                  @ loop invariant \valid(im->image + (0..state->ysize - 1));
                  @ loop invariant \valid(data + (0..(bytes - 1 - (6 + y * state->xsize))));
                  @ loop invariant \forall integer ys; 0 <= ys < state->ysize ==> \valid(im->image[ys] + (0..state->xsize - 1));
                  @ loop invariant \separated(ptr + (0..bytes - 1), im->image + (0..state->ysize - 1));
                  @ loop invariant \forall integer y; 0 <= y < state->ysize ==> \separated(ptr + (0..bytes - 1), im->image[y] + (0..state->xsize - 1));
                  @ loop invariant y < state->ysize ==> \valid(data + (0..state->xsize - 1));
                  @ loop invariant 0 <= y < state->ysize;
                  @*/
                for (y = 0; y < state->ysize; y++) {
                    UINT8 *buf_alt = im->image[y];
                    //@assert \valid(buf_alt + (0..state->xsize - 1));
                    //@assert \valid(data + (0..state->xsize - 1));
                    //@assert \separated(buf_alt + (0..state->xsize - 1), data + (0..state->xsize - 1));
                    //@assert \separated((char *)((void *)buf_alt) + (0 .. (unsigned int)state->xsize - 1), (char *)((void const *)data) + (0 .. (unsigned int)state->xsize - 1));
//                    memcpy(buf_alt, data, state->xsize);
                    data += state->xsize;
                }
                break;
            case 18:
                /* PSTAMP chunk */
                break; /* ignored */
            default:
                /* unknown chunk */
                /* printf("unknown FLI/FLC chunk: %d\n", I16_fixed(ptr+4)); */
                state->errcode = IMAGING_CODEC_UNKNOWN;
                return -1;
        }
        advance = I32_fixed(ptr);
        BAIL_ON(advance < 6 || bytes < advance);
        //@ assert advance <= bytes;
        //@ assert advance >= 6;
        ptr += advance;
        bytes -= advance;
    }

    return -1; /* end of frame */
}
