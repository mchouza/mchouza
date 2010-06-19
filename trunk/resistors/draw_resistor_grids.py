import Image, ImageDraw, ImageFont

WIDTH = 450
HEIGHT = 350
MARGIN_X = 25
MARGIN_Y = 25

def draw_text(im_draw, text, p, h, font_name, color):
    font = ImageFont.truetype(font_name + '.ttf', h)
    im_draw.text(p, text, font=font, fill=color)

def draw_resistor(imd, r, is_vert, n=3):
    points = []
    if is_vert:
        delta = (0, (r[3] - r[1]) / float(n))
        start_seq_1 = (r[2], r[1] + delta[1] / 4.0)
        start_seq_2 = (r[0], r[1] + 3.0 * delta[1] / 4.0)
        start = ((r[0] + r[2]) / 2.0, r[1])
        end = ((r[0] + r[2]) / 2.0, r[3])
    else:
        delta = ((r[2] - r[0]) / float(n), 0)
        start_seq_1 = (r[0] + delta[0] / 4.0, r[1])
        start_seq_2 = (r[0] + 3.0 * delta[0] / 4.0, r[3])
        start = (r[0], (r[1] + r[3]) / 2.0)
        end = (r[2], (r[1] + r[3]) / 2.0)
    points.append(start)
    seq1 = [(start_seq_1[0] + i * delta[0], start_seq_1[1] + i * delta[1])
            for i in range(n)]
    seq2 = [(start_seq_2[0] + i * delta[0], start_seq_2[1] + i * delta[1])
            for i in range(n)]
    points.extend(seq1[i // 2] if i % 2 == 0 else seq2[i // 2]
                  for i in range(2 * n))
    points.append(end)
    imd.line(points, fill=(0, 0, 0))

def draw_arrow(imd, p1, p2, width, arrow_size, color):
    from math import sqrt
    p1p2d = sqrt((p2[0] - p1[0]) ** 2 + (p2[1] - p1[1]) ** 2)
    delta = ((p2[0] - p1[0]) / p1p2d, (p2[1] - p1[1]) / p1p2d)
    delta_perp = (delta[1], -delta[0])
    v1 = (p2[0] + arrow_size * (delta_perp[0] - delta[0]),
          p2[1] + arrow_size * (delta_perp[1] - delta[1]))
    v2 = (p2[0] + arrow_size * (-delta_perp[0] - delta[0]),
          p2[1] + arrow_size * (-delta_perp[1] - delta[1]))
    imd.line((p1, p2), fill=color, width=width)
    imd.line((p2, v1), fill=color, width=width)
    imd.line((p2, v2), fill=color, width=width)

def draw_grid(imd, r, m, n):
    dx = (r[2] - r[0]) / (m + 2.0 / 3.0)
    dy = (r[3] - r[1]) / (n + 2.0 / 3.0)
    start_x = r[0] + dx / 3.0
    start_y = r[1] + dy / 3.0
    for i in range(m + 1):
        imd.line((start_x + dx * i, r[1], start_x + dx * i, start_y),
                 fill=(0, 0, 0))
        imd.line((start_x + dx * i, r[3], start_x + dx * i, start_y + dy * n),
                 fill=(0, 0, 0))
    for j in range(n + 1):
        imd.line((r[0], start_y + dy * j, start_x, start_y + dy * j),
                 fill=(0, 0, 0))
        imd.line((r[2], start_y + dy * j, start_x + dx * m, start_y + dy * j),
                 fill=(0, 0, 0))
    for i in range(m + 1):
        for j in range(n + 1):
            imd.ellipse((start_x + dx * i - dx / 30.0,
                         start_y + dy * j - dx / 30.0,
                         start_x + dx * i + dx / 30.0 + 1,
                         start_y + dy * j + dx / 30.0 + 1), fill=(0, 0, 0))
            if i < m:
                imd.line(((start_x + dx * i, start_y + dy * j),
                          (start_x + dx * (i + 1.0 / 3.0), start_y + dy * j)),
                         fill=(0, 0, 0))
                draw_resistor(imd,
                              (start_x + dx * (i + 1.0 / 3.0),
                               start_y + dy * j - dy / 15.0,
                               start_x + dx * (i + 2.0 / 3.0),
                               start_y + dy * j + dy / 15.0),
                              False)
                imd.line(((start_x + dx * (i + 2.0 / 3.0), start_y + dy * j),
                          (start_x + dx * (i + 1.0), start_y + dy * j)),
                         fill=(0, 0, 0))
            if j < n:
                imd.line(((start_x + dx * i, start_y + dy * j),
                          (start_x + dx * i, start_y + dy * (j + 1.0 / 3.0))),
                         fill=(0, 0, 0))
                draw_resistor(imd,
                              (start_x + dx * i - dx / 15.0,
                               start_y + dy * (j + 1.0 / 3.0),
                               start_x + dx * i + dx / 15.0,
                               start_y + dy * (j + 2.0 / 3.0)),
                              True)
                imd.line(((start_x + dx * i, start_y + dy * (j + 2.0 / 3.0)),
                          (start_x + dx * i, start_y + dy * (j + 1.0))),
                         fill=(0, 0, 0))

def draw_grid_1(fpath):
    im = Image.new('RGB', (450, 350), (255, 255, 255))
    imd = ImageDraw.Draw(im)
    
    draw_grid(imd, (25, 25, 425, 325), 4, 3)

    imd.ellipse((225 - 5, 134 - 5, 225 + 6, 134 + 6), fill=(200, 0, 0))
    draw_text(imd, 'A', (235, 140), 15, 'arial', (200, 0, 0))
    
    imd.ellipse((225 - 5, 216 - 5, 225 + 6, 216 + 6), fill=(0, 0, 200))
    draw_text(imd, 'B', (235, 223), 15, 'arial', (0, 0, 200))
    
    im.save(fpath)

def draw_grid_2(fpath):
    im = Image.new('RGB', (450, 350), (255, 255, 255))
    imd = ImageDraw.Draw(im)
    
    draw_grid(imd, (25, 25, 425, 325), 4, 3)

    imd.ellipse((225 - 5, 134 - 5, 225 + 6, 134 + 6), fill=(200, 0, 0))
    draw_text(imd, 'A', (235, 140), 15, 'arial', (200, 0, 0))
    
    draw_arrow(imd, (225 + 15, 134 + 25), (225 + 15, 134 + 55),
               1, 3, (200, 0, 0))
    draw_arrow(imd, (225 + 25, 134 - 15), (225 + 55, 134 - 15),
               1, 3, (200, 0, 0))
    draw_arrow(imd, (225 - 15, 134 - 25), (225 - 15, 134 - 55),
               1, 3, (200, 0, 0))
    draw_arrow(imd, (225 - 25, 134 + 15), (225 - 55, 134 + 15),
               1, 3, (200, 0, 0))

    draw_text(imd, '1/4', (225 + 20, 134 + 33), 12, 'arial', (200, 0, 0))
    draw_text(imd, '1/4', (225 - 34, 134 - 45), 12, 'arial', (200, 0, 0))
    draw_text(imd, '1/4', (225 - 46, 134 + 20), 12, 'arial', (200, 0, 0))
    draw_text(imd, '1/4', (225 + 33, 134 - 32), 12, 'arial', (200, 0, 0))
    
    im.save(fpath)

def draw_grid_3(fpath):
    im = Image.new('RGB', (450, 350), (255, 255, 255))
    imd = ImageDraw.Draw(im)
    
    draw_grid(imd, (25, 25, 425, 325), 4, 3)

    imd.ellipse((225 - 5, 134 - 5, 225 + 6, 134 + 6), fill=(200, 0, 0))
    draw_text(imd, 'A', (235, 140), 15, 'arial', (200, 0, 0))
    
    draw_arrow(imd, (225 + 25, 134 - 15), (225 + 55, 134 - 15),
               1, 3, (200, 0, 0))
    draw_arrow(imd, (225 - 15, 134 - 25), (225 - 15, 134 - 55),
               1, 3, (200, 0, 0))
    draw_arrow(imd, (225 - 25, 134 + 15), (225 - 55, 134 + 15),
               1, 3, (200, 0, 0))

    draw_text(imd, '?', (225 - 30, 134 - 45), 12, 'arial', (200, 0, 0))
    draw_text(imd, '?', (225 - 42, 134 + 20), 12, 'arial', (200, 0, 0))
    draw_text(imd, '?', (225 + 37, 134 - 32), 12, 'arial', (200, 0, 0))

    draw_arrow(imd, (225 + 15, 134 + 25), (225 + 15, 134 + 55),
               1, 3, (200, 0, 200))

    draw_text(imd, '1/2', (225 + 20, 134 + 33), 13, 'arial', (200, 0, 200))

    imd.ellipse((225 - 5, 216 - 5, 225 + 6, 216 + 6), fill=(0, 0, 200))
    draw_text(imd, 'B', (235, 223), 15, 'arial', (0, 0, 200))

    draw_arrow(imd, (225 + 55, 216 - 15),(225 + 25, 216 - 15), 
               1, 3, (0, 0, 200))
    draw_arrow(imd, (225 + 15, 216 + 55),(225 + 15, 216 + 25), 
               1, 3, (0, 0, 200))
    draw_arrow(imd, (225 - 55, 216 + 15),(225 - 25, 216 + 15), 
               1, 3, (0, 0, 200))

    draw_text(imd, '?', (225 - 42, 216 + 20), 12, 'arial', (0, 0, 200))
    draw_text(imd, '?', (225 + 37, 216 - 32), 12, 'arial', (0, 0, 200))
    draw_text(imd, '?', (225 + 20, 216 + 33), 12, 'arial', (0, 0, 200))
    
    im.save(fpath)

def draw_grid_4(fpath):
    im = Image.new('RGB', (450, 350), (255, 255, 255))
    imd = ImageDraw.Draw(im)
    
    draw_grid(imd, (25, 25, 425, 325), 4, 3)

    imd.ellipse((139 - 5, 134 - 5, 139 + 6, 134 + 6), fill=(200, 0, 0))
    draw_text(imd, 'A', (149, 140), 15, 'arial', (200, 0, 0))
    
    imd.ellipse((310 - 5, 216 - 5, 310 + 6, 216 + 6), fill=(0, 0, 200))
    draw_text(imd, 'B', (320, 223), 15, 'arial', (0, 0, 200))
    
    im.save(fpath)

if __name__ == '__main__':
    draw_grid_1('res_grid_1.png')
    draw_grid_2('res_grid_2.png')
    draw_grid_3('res_grid_3.png')
    draw_grid_4('res_grid_4.png')
