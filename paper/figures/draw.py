from pathlib import Path
from html import escape
P=Path(__file__).parent

def svg(name,w,h,parts):
    P.joinpath(name).write_text(f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}"><rect width="100%" height="100%" fill="white"/>'+''.join(parts)+'</svg>')
def text(x,y,s,size=17,anchor='middle'):
    return f'<text x="{x}" y="{y}" font-family="serif" font-size="{size}" text-anchor="{anchor}" fill="#172b40">{escape(s)}</text>'
def line(x,y,u,v,color='#334155',width=1.5,dash=''):
    return f'<line x1="{x}" y1="{y}" x2="{u}" y2="{v}" stroke="{color}" stroke-width="{width}" stroke-dasharray="{dash}"/>'

parts=[text(145,25,'Two-block averaging matrix'),text(475,25,'A row separates the two groups')]
a=2;b=4;e=.05;n=6
for i in range(n):
 for j in range(n):
  same=(i<a)==(j<a)
  shade='#527e9d' if i<a and j<a else '#b2c8d6' if i>=a and j>=a else '#f4f6f8'
  parts.append(f'<rect x="{55+j*30}" y="{55+i*30}" width="30" height="30" fill="{shade}" stroke="white"/>')
parts += [text(83,93,'1/a',14),text(174,178,'1/b',14),text(186,96,'0',14),text(145,266,'Pₛ : a = 2, b = 4'),text(475,262,'threshold = ε + 1/(2n)',16)]
parts += [line(345,215,640,215),line(345,215,345,52),line(345,215-(e+1/(2*n))*265,640,215-(e+1/(2*n))*265,'#a24737',1.5,'5,4'),text(652,181,'threshold',13,'start')]
for j in range(n):
 val=e+(1/a if j<a else 0);x=374+44*j;y=215-val*265
 parts+=[line(x,215,x,y,'#527e9d',4),f'<circle cx="{x}" cy="{y}" r="4" fill="#172b40"/>',text(x,239,str(j+1),13)]
parts +=[text(334,70,'ε + 1/a',13,'end'),text(334,205,'ε',13,'end')]
svg('block-rounding.svg',745,290,parts)

parts=[text(365,24,'Heavy matching enforces balanced cuts and separated mates')]
left=[(105,85),(255,85),(405,85),(555,85)];right=[(105,235),(255,235),(405,235),(555,235)]
for i,j in [(0,1),(1,2),(2,3)]:parts.append(line(*left[i],*left[j],width=2))
for i in range(4):
 parts +=[line(*left[i],*right[i],width=3,dash='6,4'),text(left[i][0]+14,164,'M',15,'start')]
for level,pts in enumerate([left,right]):
 for i,(x,y) in enumerate(pts):
  side=(i%2)^level;fill='#b2c8d6' if side else 'white'
  parts +=[f'<circle cx="{x}" cy="{y}" r="17" fill="{fill}" stroke="#172b40" stroke-width="2"/>',text(x,y+5,str(i+1)+('′' if level else ''),15)]
parts +=[text(650,90,'Original graph B',15),text(650,240,'Mate vertices',15),text(365,292,'Every accepted density cut crosses all matching edges; complementing weights reverses the objective.',14)]
svg('matching.svg',740,315,parts)

parts=[text(355,25,'Nonnegativity confines a near-optimal direction to two levels')]
parts +=[line(80,185,640,185),line(135,63,135,195,'#8a9aa8',1,'4,4'),line(575,63,575,195,'#8a9aa8',1,'4,4')]
# Diagram of (v + alpha)(beta - v): schematic horizontal scale.
parts.append('<path d="M 135 185 Q 355 -75 575 185" fill="none" stroke="#527e9d" stroke-width="2.5"/>')
for x in [135,147,163,548,567,575]:parts.append(f'<circle cx="{x}" cy="185" r="5" fill="#a24737"/>')
parts +=[text(135,216,'−α'),text(575,216,'β'),text(355,246,'Σ (vᵢ + α)(β − vᵢ) = nαβ − 1',18),text(355,273,'A small nonnegative sum forces every coordinate close to an endpoint.',15)]
svg('endpoint.svg',710,292,parts)
assert len(left)==len(right)==4
