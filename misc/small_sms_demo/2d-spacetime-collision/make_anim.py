from images2gif import writeGif
from math import *
from PIL import Image, ImageDraw, ImageFont

FONT_PATH = '/usr/share/fonts/truetype/freefont/FreeSans.ttf'

def get_cube_verts_im():
    im = Image.new('RGB', (256, 256), (255, 255, 255))
    imd = ImageDraw.Draw(im)
    return im

def make_step1_frames():
    base_im = get_cube_verts_im()
    line_sweep_frames = []
    for i in range(30):
        x = i * 256.0 / 29.0
        im = base_im.copy()
        imd = ImageDraw.Draw(im)
        imd.line(((x, 0), (x, 256)), fill=(0, 128, 0))
        line_sweep_frames.append((im, 0.1))
    im = base_im.copy()
    imd = ImageDraw.Draw(im)
    imd.ellipse(((128 - 3, 128 - 3), (128 + 3, 128 + 3)),
                (0, 0, 0))
    line_sweep_frames.append((im, 0.1))
    return line_sweep_frames

def draw_dashed_line(imd, p, q, color, num_segs, duty_cycle=0.8):
    dx = float(q[0] - p[0]) / num_segs
    dy = float(q[1] - p[1]) / num_segs
    dxon = duty_cycle * dx
    dyon = duty_cycle * dy
    xs, ys = p
    xf, yf = xs + dxon, ys + dyon
    for i in range(num_segs):
        imd.line(((xs, ys), (xf, yf)), fill=color)
        xs += dx
        ys += dy
        xf += dx
        yf += dy

def draw_line(imd, p, q, color):
    imd.line((p, q), fill=color)

def draw_circle(imd, c, r, color):
    imd.ellipse(((c[0]-r, c[1]-r), (c[0]+r, c[1]+r)), color)

def draw_centered_text(imd, text, r, color):
    font = ImageFont.truetype(FONT_PATH, r[3] - r[1])
    text_size = font.getsize(text)
    if text_size[0] > r[2] - r[0]:
        new_font_height = (r[3] - r[1]) * (r[2] - r[0]) /\
                          text_size[0]
        font = ImageFont.truetype(FONT_PATH, new_font_height)
        text_size = font.getsize(text)
    imd.text(((r[2] + r[0]) / 2 - text_size[0] / 2,
              (r[3] + r[1]) / 2 - text_size[1] / 2),
             text, font=font, fill=color)

def draw_point_label(imd, pnt, sz, letter, number, color):
    big_font = ImageFont.truetype(FONT_PATH, sz)
    small_font = ImageFont.truetype(FONT_PATH, (2 * sz) // 3)
    letter_size = big_font.getsize(letter)
    imd.text(pnt, letter, font=big_font, fill=color)
    imd.text((pnt[0] + letter_size[0], pnt[1] + sz / 2.0), number, 
             font=small_font, fill=color)

def txt_off(p):
    return (p[0] + 5, p[1] + 5)

def interp(p, q, l):
    return (p[0] * (1.0 - l) + q[0] * l, p[1] * (1.0 - l) + q[1] * l)

def make_collision_frames():
    base_im = Image.new('RGB', (256, 256), (255, 255, 255))
    frames = []

    # coordinates
    p0 = (145, 45)
    p1 = (195, 195)
    q0 = (100, 215)
    r0 = (220, 100)
    q1 = (95, 170)
    r1 = (65, 45)

    # draws p's & qr segment's trajectories
    for i in range(20):
        im = base_im.copy()
        imd = ImageDraw.Draw(im)
        p = interp(p0, p1, i / 20.0)
        q = interp(q0, q1, i / 20.0)
        r = interp(r0, r1, i / 20.0)
        color = (0, 200, 0)
        # there is a collision when 'i' is between 6 and 7
        if i == 7:
            # FIXME: DRAW COLLISION AT ITS TRUE POSITION
            draw_circle(imd, p, 3, (200, 0, 0))
            draw_point_label(imd, txt_off(p), 15, 'p', 'c', (200, 0, 0))
            base_im = im.copy()
            color = (200, 0, 0)
        # point trajectories
        draw_dashed_line(imd, p0, p, color, 10, 0.6)
        draw_dashed_line(imd, q0, q, color, 10, 0.6)
        draw_dashed_line(imd, r0, r, color, 10, 0.6)
        # p
        draw_circle(imd, p, 3, color)
        # q & r
        draw_line(imd, q, r, color)
        draw_circle(imd, q, 3, color)
        draw_circle(imd, r, 3, color)
        # p0
        draw_circle(imd, p0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(p0), 15, 'p', '0', (0, 0, 0))
        # q0 & r0
        draw_line(imd, q0, r0, (0, 0, 0))
        draw_circle(imd, q0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(q0), 15, 'q', '0', (0, 0, 0))
        draw_circle(imd, r0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(r0), 15, 'r', '0', (0, 0, 0))
        # adds the frame
        frames.append((im, 0.1))


    # draws end of p's and qr segment's trajectories
    im = base_im.copy()
    imd = ImageDraw.Draw(im)
    # trajectories
    draw_dashed_line(imd, p0, p, (0, 0, 0), 10, 0.6)
    draw_dashed_line(imd, q0, q1, (0, 0, 0), 10, 0.6)
    draw_dashed_line(imd, r0, r1, (0, 0, 0), 10, 0.6)
    # p1
    draw_circle(imd, p1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(p1), 15, 'p', '1', (0, 0, 0))
    # q1 & r1
    draw_line(imd, q1, r1, (0, 0, 0))
    draw_circle(imd, q1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(q1), 15, 'q', '1', (0, 0, 0))
    draw_circle(imd, r1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(r1), 15, 'r', '1', (0, 0, 0))
    # p0
    draw_circle(imd, p0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(p0), 15, 'p', '0', (0, 0, 0))
    # q0 & r0
    draw_line(imd, q0, r0, (0, 0, 0))
    draw_circle(imd, q0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(q0), 15, 'q', '0', (0, 0, 0))
    draw_circle(imd, r0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(r0), 15, 'r', '0', (0, 0, 0))
    # adds the frame
    frames.append((im, 2.0))

    # returns the frames
    return frames

def make_noncollision_frames():
    base_im = Image.new('RGB', (256, 256), (255, 255, 255))
    frames = []

    # coordinates
    p0 = (145, 25)
    p1 = (200, 155)
    q0 = (100, 215)
    r0 = (220, 100)
    q1 = (95, 170)
    r1 = (65, 45)

    # draws p's & qr segment's trajectories
    for i in range(20):
        im = base_im.copy()
        imd = ImageDraw.Draw(im)
        p = interp(p0, p1, i / 20.0)
        q = interp(q0, q1, i / 20.0)
        r = interp(r0, r1, i / 20.0)
        color = (0, 200, 0)
        # point trajectories
        draw_dashed_line(imd, p0, p, color, 10, 0.6)
        draw_dashed_line(imd, q0, q, color, 10, 0.6)
        draw_dashed_line(imd, r0, r, color, 10, 0.6)
        # p
        draw_circle(imd, p, 3, color)
        # q & r
        draw_line(imd, q, r, color)
        draw_circle(imd, q, 3, color)
        draw_circle(imd, r, 3, color)
        # p0
        draw_circle(imd, p0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(p0), 15, 'p', '0', (0, 0, 0))
        # q0 & r0
        draw_line(imd, q0, r0, (0, 0, 0))
        draw_circle(imd, q0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(q0), 15, 'q', '0', (0, 0, 0))
        draw_circle(imd, r0, 3, (0, 0, 0))
        draw_point_label(imd, txt_off(r0), 15, 'r', '0', (0, 0, 0))
        # adds the frame
        frames.append((im, 0.1))


    # draws end of p's and qr segment's trajectories
    im = base_im.copy()
    imd = ImageDraw.Draw(im)
    # trajectories
    draw_dashed_line(imd, p0, p, (0, 0, 0), 10, 0.6)
    draw_dashed_line(imd, q0, q1, (0, 0, 0), 10, 0.6)
    draw_dashed_line(imd, r0, r1, (0, 0, 0), 10, 0.6)
    # p1
    draw_circle(imd, p1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(p1), 15, 'p', '1', (0, 0, 0))
    # q1 & r1
    draw_line(imd, q1, r1, (0, 0, 0))
    draw_circle(imd, q1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(q1), 15, 'q', '1', (0, 0, 0))
    draw_circle(imd, r1, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(r1), 15, 'r', '1', (0, 0, 0))
    # p0
    draw_circle(imd, p0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(p0), 15, 'p', '0', (0, 0, 0))
    # q0 & r0
    draw_line(imd, q0, r0, (0, 0, 0))
    draw_circle(imd, q0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(q0), 15, 'q', '0', (0, 0, 0))
    draw_circle(imd, r0, 3, (0, 0, 0))
    draw_point_label(imd, txt_off(r0), 15, 'r', '0', (0, 0, 0))
    # adds the frame
    frames.append((im, 2.0))

    # returns the frames
    return frames

def main():
    frames = make_collision_frames()
    frames += make_noncollision_frames()
    frames, durations = zip(*frames)
    writeGif("anim.gif", frames, duration=durations, loops=3, dither=0)

if __name__ == '__main__':
    main()
