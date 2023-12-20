#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 15:34:06 2023


This file is to generate all sequences of forests where each tree has at least 2 vertices of size between 2 and n vertices with n growing to 2 up to maxn vertices
"""

import csv
import pandas as pd
import numpy as np
import time
from utility_to_gen_all_foret import gen_foret_taille_max
import sys


 

taille_max_foret = int(sys.argv[1])


foret_sans_point_isole = gen_foret_taille_max(taille_max_foret,False,True).sort_values(by="v")
foret_sans_point_isole.to_csv("foret_sans_point_isole_" +str(taille_max_foret)+ ".csv")

combinaisons_list = [(['v', 'maxt'], 1),
 (['v', 'mint'], 2),
 (['v', 'maxp'], 3),
 (['v', 'minp'], 4),
 (['v', 'maxd'], 5),
 (['v', 'mind'], 6),
 (['v', 'maxf'], 7),
 (['v', 'minf'], 8),
 (['v', 'f'], 9),
 (['v', 't'], 10),
 (['v', 'maxt', 't'], 11),
 (['v', 'maxt', 'f'], 12),
 (['v', 'maxt', 'minf'], 13),
 (['v', 'maxt', 'maxf'], 14),
 (['v', 'maxt', 'mind'], 15),
 (['v', 'maxt', 'maxd'], 16),
 (['v', 'maxt', 'minp'], 17),
 (['v', 'maxt', 'maxp'], 18),
 (['v', 'maxt', 'mint'], 19),
 (['v', 'mint', 'maxt'], 20),
 (['v', 'mint', 't'], 21),
 (['v', 'mint', 'f'], 22),
 (['v', 'mint', 'minf'], 23),
 (['v', 'mint', 'maxf'], 24),
 (['v', 'mint', 'mind'], 25),
 (['v', 'mint', 'maxd'], 26),
 (['v', 'mint', 'minp'], 27),
 (['v', 'mint', 'maxp'], 28),
 (['v', 'maxp', 'mint'], 29),
 (['v', 'maxp', 'maxt'], 30),
 (['v', 'maxp', 't'], 31),
 (['v', 'maxp', 'f'], 32),
 (['v', 'maxp', 'minf'], 33),
 (['v', 'maxp', 'maxf'], 34),
 (['v', 'maxp', 'mind'], 35),
 (['v', 'maxp', 'maxd'], 36),
 (['v', 'maxp', 'minp'], 37),
 (['v', 'minp', 'maxp'], 38),
 (['v', 'minp', 'mint'], 39),
 (['v', 'minp', 'maxt'], 40),
 (['v', 'minp', 't'], 41),
 (['v', 'minp', 'f'], 42),
 (['v', 'minp', 'minf'], 43),
 (['v', 'minp', 'maxf'], 44),
 (['v', 'minp', 'mind'], 45),
 (['v', 'minp', 'maxd'], 46),
 (['v', 'maxd', 'minp'], 47),
 (['v', 'maxd', 'maxp'], 48),
 (['v', 'maxd', 'mint'], 49),
 (['v', 'maxd', 'maxt'], 50),
 (['v', 'maxd', 't'], 51),
 (['v', 'maxd', 'f'], 52),
 (['v', 'maxd', 'minf'], 53),
 (['v', 'maxd', 'maxf'], 54),
 (['v', 'maxd', 'mind'], 55),
 (['v', 'mind', 'maxd'], 56),
 (['v', 'mind', 'minp'], 57),
 (['v', 'mind', 'maxp'], 58),
 (['v', 'mind', 'mint'], 59),
 (['v', 'mind', 'maxt'], 60),
 (['v', 'mind', 't'], 61),
 (['v', 'mind', 'f'], 62),
 (['v', 'mind', 'minf'], 63),
 (['v', 'mind', 'maxf'], 64),
 (['v', 'maxf', 'mind'], 65),
 (['v', 'maxf', 'maxd'], 66),
 (['v', 'maxf', 'minp'], 67),
 (['v', 'maxf', 'maxp'], 68),
 (['v', 'maxf', 'mint'], 69),
 (['v', 'maxf', 'maxt'], 70),
 (['v', 'maxf', 't'], 71),
 (['v', 'maxf', 'f'], 72),
 (['v', 'maxf', 'minf'], 73),
 (['v', 'minf', 'maxf'], 74),
 (['v', 'minf', 'mind'], 75),
 (['v', 'minf', 'maxd'], 76),
 (['v', 'minf', 'minp'], 77),
 (['v', 'minf', 'maxp'], 78),
 (['v', 'minf', 'mint'], 79),
 (['v', 'minf', 'maxt'], 80),
 (['v', 'minf', 't'], 81),
 (['v', 'minf', 'f'], 82),
 (['v', 'f', 'minf'], 83),
 (['v', 'f', 'maxf'], 84),
 (['v', 'f', 'mind'], 85),
 (['v', 'f', 'maxd'], 86),
 (['v', 'f', 'minp'], 87),
 (['v', 'f', 'maxp'], 88),
 (['v', 'f', 'mint'], 89),
 (['v', 'f', 'maxt'], 90),
 (['v', 'f', 't'], 91),
 (['v', 't', 'f'], 92),
 (['v', 't', 'minf'], 93),
 (['v', 't', 'maxf'], 94),
 (['v', 't', 'mind'], 95),
 (['v', 't', 'maxd'], 96),
 (['v', 't', 'minp'], 97),
 (['v', 't', 'maxp'], 98),
 (['v', 't', 'mint'], 99),
 (['v', 't', 'maxt'], 100),
 (['v', 'mint', 'maxt', 't'], 101),
 (['v', 'mint', 'maxt', 'f'], 102),
 (['v', 'mint', 'maxt', 'minf'], 103),
 (['v', 'mint', 'maxt', 'maxf'], 104),
 (['v', 'mint', 'maxt', 'mind'], 105),
 (['v', 'mint', 'maxt', 'maxd'], 106),
 (['v', 'mint', 'maxt', 'minp'], 107),
 (['v', 'mint', 'maxt', 'maxp'], 108),
 (['v', 'maxp', 'mint', 'maxt'], 109),
 (['v', 'maxp', 'mint', 't'], 110),
 (['v', 'maxp', 'mint', 'f'], 111),
 (['v', 'maxp', 'mint', 'minf'], 112),
 (['v', 'maxp', 'mint', 'maxf'], 113),
 (['v', 'maxp', 'mint', 'mind'], 114),
 (['v', 'maxp', 'mint', 'maxd'], 115),
 (['v', 'maxp', 'mint', 'minp'], 116),
 (['v', 'maxp', 'maxt', 'mint'], 117),
 (['v', 'maxp', 'maxt', 't'], 118),
 (['v', 'maxp', 'maxt', 'f'], 119),
 (['v', 'maxp', 'maxt', 'minf'], 120),
 (['v', 'maxp', 'maxt', 'maxf'], 121),
 (['v', 'maxp', 'maxt', 'mind'], 122),
 (['v', 'maxp', 'maxt', 'maxd'], 123),
 (['v', 'maxp', 'maxt', 'minp'], 124),
 (['v', 'minp', 'maxp', 'maxt'], 125),
 (['v', 'minp', 'maxp', 'mint'], 126),
 (['v', 'minp', 'maxp', 't'], 127),
 (['v', 'minp', 'maxp', 'f'], 128),
 (['v', 'minp', 'maxp', 'minf'], 129),
 (['v', 'minp', 'maxp', 'maxf'], 130),
 (['v', 'minp', 'maxp', 'mind'], 131),
 (['v', 'minp', 'maxp', 'maxd'], 132),
 (['v', 'minp', 'mint', 'maxp'], 133),
 (['v', 'minp', 'mint', 'maxt'], 134),
 (['v', 'minp', 'mint', 't'], 135),
 (['v', 'minp', 'mint', 'f'], 136),
 (['v', 'minp', 'mint', 'minf'], 137),
 (['v', 'minp', 'mint', 'maxf'], 138),
 (['v', 'minp', 'mint', 'mind'], 139),
 (['v', 'minp', 'mint', 'maxd'], 140),
 (['v', 'minp', 'maxt', 'mint'], 141),
 (['v', 'minp', 'maxt', 'maxp'], 142),
 (['v', 'minp', 'maxt', 't'], 143),
 (['v', 'minp', 'maxt', 'f'], 144),
 (['v', 'minp', 'maxt', 'minf'], 145),
 (['v', 'minp', 'maxt', 'maxf'], 146),
 (['v', 'minp', 'maxt', 'mind'], 147),
 (['v', 'minp', 'maxt', 'maxd'], 148),
 (['v', 'maxd', 'minp', 'maxt'], 149),
 (['v', 'maxd', 'minp', 'mint'], 150),
 (['v', 'maxd', 'minp', 'maxp'], 151),
 (['v', 'maxd', 'minp', 't'], 152),
 (['v', 'maxd', 'minp', 'f'], 153),
 (['v', 'maxd', 'minp', 'minf'], 154),
 (['v', 'maxd', 'minp', 'maxf'], 155),
 (['v', 'maxd', 'minp', 'mind'], 156),
 (['v', 'maxd', 'maxp', 'minp'], 157),
 (['v', 'maxd', 'maxp', 'maxt'], 158),
 (['v', 'maxd', 'maxp', 'mint'], 159),
 (['v', 'maxd', 'maxp', 't'], 160),
 (['v', 'maxd', 'maxp', 'f'], 161),
 (['v', 'maxd', 'maxp', 'minf'], 162),
 (['v', 'maxd', 'maxp', 'maxf'], 163),
 (['v', 'maxd', 'maxp', 'mind'], 164),
 (['v', 'maxd', 'mint', 'maxp'], 165),
 (['v', 'maxd', 'mint', 'minp'], 166),
 (['v', 'maxd', 'mint', 'maxt'], 167),
 (['v', 'maxd', 'mint', 't'], 168),
 (['v', 'maxd', 'mint', 'f'], 169),
 (['v', 'maxd', 'mint', 'minf'], 170),
 (['v', 'maxd', 'mint', 'maxf'], 171),
 (['v', 'maxd', 'mint', 'mind'], 172),
 (['v', 'maxd', 'maxt', 'mint'], 173),
 (['v', 'maxd', 'maxt', 'maxp'], 174),
 (['v', 'maxd', 'maxt', 'minp'], 175),
 (['v', 'maxd', 'maxt', 't'], 176),
 (['v', 'maxd', 'maxt', 'f'], 177),
 (['v', 'maxd', 'maxt', 'minf'], 178),
 (['v', 'maxd', 'maxt', 'maxf'], 179),
 (['v', 'maxd', 'maxt', 'mind'], 180),
 (['v', 'mind', 'maxd', 'maxt'], 181),
 (['v', 'mind', 'maxd', 'mint'], 182),
 (['v', 'mind', 'maxd', 'maxp'], 183),
 (['v', 'mind', 'maxd', 'minp'], 184),
 (['v', 'mind', 'maxd', 't'], 185),
 (['v', 'mind', 'maxd', 'f'], 186),
 (['v', 'mind', 'maxd', 'minf'], 187),
 (['v', 'mind', 'maxd', 'maxf'], 188),
 (['v', 'mind', 'minp', 'maxd'], 189),
 (['v', 'mind', 'minp', 'maxt'], 190),
 (['v', 'mind', 'minp', 'mint'], 191),
 (['v', 'mind', 'minp', 'maxp'], 192),
 (['v', 'mind', 'minp', 't'], 193),
 (['v', 'mind', 'minp', 'f'], 194),
 (['v', 'mind', 'minp', 'minf'], 195),
 (['v', 'mind', 'minp', 'maxf'], 196),
 (['v', 'mind', 'maxp', 'minp'], 197),
 (['v', 'mind', 'maxp', 'maxd'], 198),
 (['v', 'mind', 'maxp', 'maxt'], 199),
 (['v', 'mind', 'maxp', 'mint'], 200),
 (['v', 'mind', 'maxp', 't'], 201),
 (['v', 'mind', 'maxp', 'f'], 202),
 (['v', 'mind', 'maxp', 'minf'], 203),
 (['v', 'mind', 'maxp', 'maxf'], 204),
 (['v', 'mind', 'mint', 'maxp'], 205),
 (['v', 'mind', 'mint', 'minp'], 206),
 (['v', 'mind', 'mint', 'maxd'], 207),
 (['v', 'mind', 'mint', 'maxt'], 208),
 (['v', 'mind', 'mint', 't'], 209),
 (['v', 'mind', 'mint', 'f'], 210),
 (['v', 'mind', 'mint', 'minf'], 211),
 (['v', 'mind', 'mint', 'maxf'], 212),
 (['v', 'mind', 'maxt', 'mint'], 213),
 (['v', 'mind', 'maxt', 'maxp'], 214),
 (['v', 'mind', 'maxt', 'minp'], 215),
 (['v', 'mind', 'maxt', 'maxd'], 216),
 (['v', 'mind', 'maxt', 't'], 217),
 (['v', 'mind', 'maxt', 'f'], 218),
 (['v', 'mind', 'maxt', 'minf'], 219),
 (['v', 'mind', 'maxt', 'maxf'], 220),
 (['v', 'maxf', 'mind', 'maxt'], 221),
 (['v', 'maxf', 'mind', 'mint'], 222),
 (['v', 'maxf', 'mind', 'maxp'], 223),
 (['v', 'maxf', 'mind', 'minp'], 224),
 (['v', 'maxf', 'mind', 'maxd'], 225),
 (['v', 'maxf', 'mind', 't'], 226),
 (['v', 'maxf', 'mind', 'f'], 227),
 (['v', 'maxf', 'mind', 'minf'], 228),
 (['v', 'maxf', 'maxd', 'mind'], 229),
 (['v', 'maxf', 'maxd', 'maxt'], 230),
 (['v', 'maxf', 'maxd', 'mint'], 231),
 (['v', 'maxf', 'maxd', 'maxp'], 232),
 (['v', 'maxf', 'maxd', 'minp'], 233),
 (['v', 'maxf', 'maxd', 't'], 234),
 (['v', 'maxf', 'maxd', 'f'], 235),
 (['v', 'maxf', 'maxd', 'minf'], 236),
 (['v', 'maxf', 'minp', 'maxd'], 237),
 (['v', 'maxf', 'minp', 'mind'], 238),
 (['v', 'maxf', 'minp', 'maxt'], 239),
 (['v', 'maxf', 'minp', 'mint'], 240),
 (['v', 'maxf', 'minp', 'maxp'], 241),
 (['v', 'maxf', 'minp', 't'], 242),
 (['v', 'maxf', 'minp', 'f'], 243),
 (['v', 'maxf', 'minp', 'minf'], 244),
 (['v', 'maxf', 'maxp', 'minp'], 245),
 (['v', 'maxf', 'maxp', 'maxd'], 246),
 (['v', 'maxf', 'maxp', 'mind'], 247),
 (['v', 'maxf', 'maxp', 'maxt'], 248),
 (['v', 'maxf', 'maxp', 'mint'], 249),
 (['v', 'maxf', 'maxp', 't'], 250),
 (['v', 'maxf', 'maxp', 'f'], 251),
 (['v', 'maxf', 'maxp', 'minf'], 252),
 (['v', 'maxf', 'mint', 'maxp'], 253),
 (['v', 'maxf', 'mint', 'minp'], 254),
 (['v', 'maxf', 'mint', 'maxd'], 255),
 (['v', 'maxf', 'mint', 'mind'], 256),
 (['v', 'maxf', 'mint', 'maxt'], 257),
 (['v', 'maxf', 'mint', 't'], 258),
 (['v', 'maxf', 'mint', 'f'], 259),
 (['v', 'maxf', 'mint', 'minf'], 260),
 (['v', 'maxf', 'maxt', 'mint'], 261),
 (['v', 'maxf', 'maxt', 'maxp'], 262),
 (['v', 'maxf', 'maxt', 'minp'], 263),
 (['v', 'maxf', 'maxt', 'maxd'], 264),
 (['v', 'maxf', 'maxt', 'mind'], 265),
 (['v', 'maxf', 'maxt', 't'], 266),
 (['v', 'maxf', 'maxt', 'f'], 267),
 (['v', 'maxf', 'maxt', 'minf'], 268),
 (['v', 'minf', 'maxf', 'maxt'], 269),
 (['v', 'minf', 'maxf', 'mint'], 270),
 (['v', 'minf', 'maxf', 'maxp'], 271),
 (['v', 'minf', 'maxf', 'minp'], 272),
 (['v', 'minf', 'maxf', 'maxd'], 273),
 (['v', 'minf', 'maxf', 'mind'], 274),
 (['v', 'minf', 'maxf', 't'], 275),
 (['v', 'minf', 'maxf', 'f'], 276),
 (['v', 'minf', 'mind', 'maxf'], 277),
 (['v', 'minf', 'mind', 'maxt'], 278),
 (['v', 'minf', 'mind', 'mint'], 279),
 (['v', 'minf', 'mind', 'maxp'], 280),
 (['v', 'minf', 'mind', 'minp'], 281),
 (['v', 'minf', 'mind', 'maxd'], 282),
 (['v', 'minf', 'mind', 't'], 283),
 (['v', 'minf', 'mind', 'f'], 284),
 (['v', 'minf', 'maxd', 'mind'], 285),
 (['v', 'minf', 'maxd', 'maxf'], 286),
 (['v', 'minf', 'maxd', 'maxt'], 287),
 (['v', 'minf', 'maxd', 'mint'], 288),
 (['v', 'minf', 'maxd', 'maxp'], 289),
 (['v', 'minf', 'maxd', 'minp'], 290),
 (['v', 'minf', 'maxd', 't'], 291),
 (['v', 'minf', 'maxd', 'f'], 292),
 (['v', 'minf', 'minp', 'maxd'], 293),
 (['v', 'minf', 'minp', 'mind'], 294),
 (['v', 'minf', 'minp', 'maxf'], 295),
 (['v', 'minf', 'minp', 'maxt'], 296),
 (['v', 'minf', 'minp', 'mint'], 297),
 (['v', 'minf', 'minp', 'maxp'], 298),
 (['v', 'minf', 'minp', 't'], 299),
 (['v', 'minf', 'minp', 'f'], 300),
 (['v', 'minf', 'maxp', 'minp'], 301),
 (['v', 'minf', 'maxp', 'maxd'], 302),
 (['v', 'minf', 'maxp', 'mind'], 303),
 (['v', 'minf', 'maxp', 'maxf'], 304),
 (['v', 'minf', 'maxp', 'maxt'], 305),
 (['v', 'minf', 'maxp', 'mint'], 306),
 (['v', 'minf', 'maxp', 't'], 307),
 (['v', 'minf', 'maxp', 'f'], 308),
 (['v', 'minf', 'mint', 'maxp'], 309),
 (['v', 'minf', 'mint', 'minp'], 310),
 (['v', 'minf', 'mint', 'maxd'], 311),
 (['v', 'minf', 'mint', 'mind'], 312),
 (['v', 'minf', 'mint', 'maxf'], 313),
 (['v', 'minf', 'mint', 'maxt'], 314),
 (['v', 'minf', 'mint', 't'], 315),
 (['v', 'minf', 'mint', 'f'], 316),
 (['v', 'minf', 'maxt', 'mint'], 317),
 (['v', 'minf', 'maxt', 'maxp'], 318),
 (['v', 'minf', 'maxt', 'minp'], 319),
 (['v', 'minf', 'maxt', 'maxd'], 320),
 (['v', 'minf', 'maxt', 'mind'], 321),
 (['v', 'minf', 'maxt', 'maxf'], 322),
 (['v', 'minf', 'maxt', 't'], 323),
 (['v', 'minf', 'maxt', 'f'], 324),
 (['v', 'f', 'minf', 'maxt'], 325),
 (['v', 'f', 'minf', 'mint'], 326),
 (['v', 'f', 'minf', 'maxp'], 327),
 (['v', 'f', 'minf', 'minp'], 328),
 (['v', 'f', 'minf', 'maxd'], 329),
 (['v', 'f', 'minf', 'mind'], 330),
 (['v', 'f', 'minf', 'maxf'], 331),
 (['v', 'f', 'minf', 't'], 332),
 (['v', 'f', 'maxf', 'minf'], 333),
 (['v', 'f', 'maxf', 'maxt'], 334),
 (['v', 'f', 'maxf', 'mint'], 335),
 (['v', 'f', 'maxf', 'maxp'], 336),
 (['v', 'f', 'maxf', 'minp'], 337),
 (['v', 'f', 'maxf', 'maxd'], 338),
 (['v', 'f', 'maxf', 'mind'], 339),
 (['v', 'f', 'maxf', 't'], 340),
 (['v', 'f', 'mind', 'maxf'], 341),
 (['v', 'f', 'mind', 'minf'], 342),
 (['v', 'f', 'mind', 'maxt'], 343),
 (['v', 'f', 'mind', 'mint'], 344),
 (['v', 'f', 'mind', 'maxp'], 345),
 (['v', 'f', 'mind', 'minp'], 346),
 (['v', 'f', 'mind', 'maxd'], 347),
 (['v', 'f', 'mind', 't'], 348),
 (['v', 'f', 'maxd', 'mind'], 349),
 (['v', 'f', 'maxd', 'maxf'], 350),
 (['v', 'f', 'maxd', 'minf'], 351),
 (['v', 'f', 'maxd', 'maxt'], 352),
 (['v', 'f', 'maxd', 'mint'], 353),
 (['v', 'f', 'maxd', 'maxp'], 354),
 (['v', 'f', 'maxd', 'minp'], 355),
 (['v', 'f', 'maxd', 't'], 356),
 (['v', 'f', 'minp', 'maxd'], 357),
 (['v', 'f', 'minp', 'mind'], 358),
 (['v', 'f', 'minp', 'maxf'], 359),
 (['v', 'f', 'minp', 'minf'], 360),
 (['v', 'f', 'minp', 'maxt'], 361),
 (['v', 'f', 'minp', 'mint'], 362),
 (['v', 'f', 'minp', 'maxp'], 363),
 (['v', 'f', 'minp', 't'], 364),
 (['v', 'f', 'maxp', 'minp'], 365),
 (['v', 'f', 'maxp', 'maxd'], 366),
 (['v', 'f', 'maxp', 'mind'], 367),
 (['v', 'f', 'maxp', 'maxf'], 368),
 (['v', 'f', 'maxp', 'minf'], 369),
 (['v', 'f', 'maxp', 'maxt'], 370),
 (['v', 'f', 'maxp', 'mint'], 371),
 (['v', 'f', 'maxp', 't'], 372),
 (['v', 'f', 'mint', 'maxp'], 373),
 (['v', 'f', 'mint', 'minp'], 374),
 (['v', 'f', 'mint', 'maxd'], 375),
 (['v', 'f', 'mint', 'mind'], 376),
 (['v', 'f', 'mint', 'maxf'], 377),
 (['v', 'f', 'mint', 'minf'], 378),
 (['v', 'f', 'mint', 'maxt'], 379),
 (['v', 'f', 'mint', 't'], 380),
 (['v', 'f', 'maxt', 'mint'], 381),
 (['v', 'f', 'maxt', 'maxp'], 382),
 (['v', 'f', 'maxt', 'minp'], 383),
 (['v', 'f', 'maxt', 'maxd'], 384),
 (['v', 'f', 'maxt', 'mind'], 385),
 (['v', 'f', 'maxt', 'maxf'], 386),
 (['v', 'f', 'maxt', 'minf'], 387),
 (['v', 'f', 'maxt', 't'], 388),
 (['v', 't', 'f', 'maxt'], 389),
 (['v', 't', 'f', 'mint'], 390),
 (['v', 't', 'f', 'maxp'], 391),
 (['v', 't', 'f', 'minp'], 392),
 (['v', 't', 'f', 'maxd'], 393),
 (['v', 't', 'f', 'mind'], 394),
 (['v', 't', 'f', 'maxf'], 395),
 (['v', 't', 'f', 'minf'], 396),
 (['v', 't', 'minf', 'f'], 397),
 (['v', 't', 'minf', 'maxt'], 398),
 (['v', 't', 'minf', 'mint'], 399),
 (['v', 't', 'minf', 'maxp'], 400),
 (['v', 't', 'minf', 'minp'], 401),
 (['v', 't', 'minf', 'maxd'], 402),
 (['v', 't', 'minf', 'mind'], 403),
 (['v', 't', 'minf', 'maxf'], 404),
 (['v', 't', 'maxf', 'minf'], 405),
 (['v', 't', 'maxf', 'f'], 406),
 (['v', 't', 'maxf', 'maxt'], 407),
 (['v', 't', 'maxf', 'mint'], 408),
 (['v', 't', 'maxf', 'maxp'], 409),
 (['v', 't', 'maxf', 'minp'], 410),
 (['v', 't', 'maxf', 'maxd'], 411),
 (['v', 't', 'maxf', 'mind'], 412),
 (['v', 't', 'mind', 'maxf'], 413),
 (['v', 't', 'mind', 'minf'], 414),
 (['v', 't', 'mind', 'f'], 415),
 (['v', 't', 'mind', 'maxt'], 416),
 (['v', 't', 'mind', 'mint'], 417),
 (['v', 't', 'mind', 'maxp'], 418),
 (['v', 't', 'mind', 'minp'], 419),
 (['v', 't', 'mind', 'maxd'], 420),
 (['v', 't', 'maxd', 'mind'], 421),
 (['v', 't', 'maxd', 'maxf'], 422),
 (['v', 't', 'maxd', 'minf'], 423),
 (['v', 't', 'maxd', 'f'], 424),
 (['v', 't', 'maxd', 'maxt'], 425),
 (['v', 't', 'maxd', 'mint'], 426),
 (['v', 't', 'maxd', 'maxp'], 427),
 (['v', 't', 'maxd', 'minp'], 428),
 (['v', 't', 'minp', 'maxd'], 429),
 (['v', 't', 'minp', 'mind'], 430),
 (['v', 't', 'minp', 'maxf'], 431),
 (['v', 't', 'minp', 'minf'], 432),
 (['v', 't', 'minp', 'f'], 433),
 (['v', 't', 'minp', 'maxt'], 434),
 (['v', 't', 'minp', 'mint'], 435),
 (['v', 't', 'minp', 'maxp'], 436),
 (['v', 't', 'maxp', 'minp'], 437),
 (['v', 't', 'maxp', 'maxd'], 438),
 (['v', 't', 'maxp', 'mind'], 439),
 (['v', 't', 'maxp', 'maxf'], 440),
 (['v', 't', 'maxp', 'minf'], 441),
 (['v', 't', 'maxp', 'f'], 442),
 (['v', 't', 'maxp', 'maxt'], 443),
 (['v', 't', 'maxp', 'mint'], 444),
 (['v', 't', 'mint', 'maxp'], 445),
 (['v', 't', 'mint', 'minp'], 446),
 (['v', 't', 'mint', 'maxd'], 447),
 (['v', 't', 'mint', 'mind'], 448),
 (['v', 't', 'mint', 'maxf'], 449),
 (['v', 't', 'mint', 'minf'], 450),
 (['v', 't', 'mint', 'f'], 451),
 (['v', 't', 'mint', 'maxt'], 452),
 (['v', 't', 'maxt', 'mint'], 453),
 (['v', 't', 'maxt', 'maxp'], 454),
 (['v', 't', 'maxt', 'minp'], 455),
 (['v', 't', 'maxt', 'maxd'], 456),
 (['v', 't', 'maxt', 'mind'], 457),
 (['v', 't', 'maxt', 'maxf'], 458),
 (['v', 't', 'maxt', 'minf'], 459),
 (['v', 't', 'maxt', 'f'], 460)]
 
def initial_dic_comb_dic_value(combinaisons,list_carac_names):
    #tps1 = time.time()
    dic_comb_dic_value = {}
    for (combinaison,ind_comb) in combinaisons:
        dic_comb_dic_value[ind_comb] = {}
        dic_comb_dic_value[ind_comb]["att"] = list_carac_names
    #tps2 = time.time()
    #print("initial_dic_comb_dic_value made:",tps2-tps1,"s")
    return dic_comb_dic_value

def get_complement_comb(combinaison,list_carac_names):
    compl_comb = []
    for att_string in list_carac_names:
        if att_string not in combinaison:
                compl_comb.append(att_string)
    return compl_comb

def transform_row_key(row,combinaison):
    row_comb_values_entries = "["+row[combinaison[0]]
    for att_string in combinaison[1:-1]:
            row_comb_values_entries = row_comb_values_entries + "," + row[att_string]
    row_comb_values_entries = row_comb_values_entries + "]"
    return row_comb_values_entries

    
    
def delete_undependant_sec(row0,row,cur_list_atts):
    
    new_list_atts = []
    for att in cur_list_atts:
        if row0[att] == row[att]:
            new_list_atts.append(att)
    return new_list_atts

def buil_row_dependant_sec(row,cur_list_atts):
    
    row_dependant_sec = {}
    for att in cur_list_atts:
        row_dependant_sec[att] = row[att]
    return row_dependant_sec

def gen_name_datatable(combinaison):
    name_datatable = ""
    for param in combinaison:
        param_sans_moins = param.replace('-','').lower()
        name_datatable =  name_datatable + "_" + param_sans_moins                    
    return name_datatable

def write_ext_table(combinaison,ind_comb,dic_comb_dic_value,lowup):
    cur_list_atts = dic_comb_dic_value[ind_comb]["att"]
    compl_comb = get_complement_comb(combinaison,cur_list_atts)
    ext_data = []
    for ext_row in dic_comb_dic_value[ind_comb].values():
        if ext_row != dic_comb_dic_value[ind_comb]["att"]:
            ext_data.append(ext_row)
    df = pd.DataFrame(data = ext_data, columns = cur_list_atts)[combinaison + compl_comb]
    if lowup == "up":
        df.to_csv("ext_forest0/up"+gen_name_datatable(combinaison)+".csv")
    else:
        df.to_csv("ext_forest0/low"+gen_name_datatable(combinaison)+".csv")
    return df


def gen_forest_csv_tables(combinaisons_list,list_carac_names,lowup):
    tps1 = time.time()
    dic_comb_dic_value = initial_dic_comb_dic_value(combinaisons_list,list_carac_names)
    with open("foret_sans_point_isole_"+str(taille_max_foret)+".csv", newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            
            for row in reader:
                for (combinaison,ind_comb) in combinaisons_list:
                    output = combinaison[-1]
                    row_key_entry = transform_row_key(row,combinaison)
                    if row_key_entry not in dic_comb_dic_value[ind_comb].keys():
                                            dic_comb_dic_value[ind_comb][row_key_entry] = row
               
                    elif lowup == "up" :
                          if int(dic_comb_dic_value[ind_comb][row_key_entry][output]) < int(row[output]):
                                dic_comb_dic_value[ind_comb][row_key_entry] = row
                                
                    elif lowup == "low" :
                          if int(dic_comb_dic_value[ind_comb][row_key_entry][output]) > int(row[output]):
                                dic_comb_dic_value[ind_comb][row_key_entry] = row
                                
    with open("foret_sans_point_isole_"+str(taille_max_foret)+".csv", newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            
            for row in reader:
                for (combinaison,ind_comb) in combinaisons_list:
                    output = combinaison[-1]
                    row_key_entry = transform_row_key(row,combinaison)
                    
                    if    dic_comb_dic_value[ind_comb][row_key_entry][output] == row[output]:
                            new_list_att = delete_undependant_sec(dic_comb_dic_value[ind_comb][row_key_entry],row,dic_comb_dic_value[ind_comb]["att"])
                            dic_comb_dic_value[ind_comb]["att"] = new_list_att
                          
    for (combinaison,ind_comb) in combinaisons_list:
        for row in dic_comb_dic_value[ind_comb].values():
            
            if row != dic_comb_dic_value[ind_comb]["att"]:
                row_key_entry = transform_row_key(row,combinaison)
                row_dependant_sec = buil_row_dependant_sec(row,dic_comb_dic_value[ind_comb]["att"])
                dic_comb_dic_value[ind_comb][row_key_entry] = row_dependant_sec
        write_ext_table(combinaison,ind_comb,dic_comb_dic_value,lowup)        
    tps2 = time.time()
    print("gen_forest_csv_tables made:",tps2-tps1,"s")

list_carac_names = ["v", "t","f","minf","maxf","mind","maxd", "minp","maxp","mint","maxt"]
gen_forest_csv_tables(combinaisons_list,list_carac_names,"up")
gen_forest_csv_tables(combinaisons_list,list_carac_names,"low")


def ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param):
    list_parametres = ""
    k = 0
    for parametre in dataframe_tabledata.columns[1:-1]:
        k = k + 1
        param_sans_moins = parametre.replace('-','').lower()
        if param_sans_moins == bounded:
            list_parametres = list_parametres + "t("+param_sans_moins+","+lowup+",output),\n"
        elif k <= nb_param : 
            list_parametres = list_parametres + "t("+param_sans_moins+",primary,input),\n"
        else:
            list_parametres = list_parametres + "t("+param_sans_moins+",secondary,input),\n" 
    
           
    if dataframe_tabledata.columns[-1] == bounded:
        list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+","+lowup+",output)\n"
    else:
        list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+",secondary,input)\n"  
    return list_parametres

def ecrire_un_fait(nom_de_la_table,entreetable):
    fait = nom_de_la_table+"("
    for valeur in entreetable[1:-1]:
        fait = fait + str(int(valeur))+","
    fait = fait + str(int(entreetable[-1])) + ").\n" 
    return fait
        
def ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata):
    list_faits_prolog = ""
    for entreetable in dataframe_tabledata.values.tolist():
        list_faits_prolog = list_faits_prolog + ecrire_un_fait(nom_de_la_table,entreetable)
    return list_faits_prolog
    

    
def trans_allfeaturestabledata_prolog(nom_de_la_tab,dataframe_tabledata,lowup,maxn,bounded,nb_param,objet_combinatoire):
    nom_de_la_table = lowup+nom_de_la_tab
    nom_table_prolog = "data_"+objet_combinatoire+"/data"+str(maxn)+"/" + nom_de_la_table + ".pl"
    nb_col = dataframe_tabledata.shape[1]-1
    fichier0 = open(nom_table_prolog, "w")
    fichier0.write(":- multifile signature/3.\n"+
                  ":- multifile "+ nom_de_la_table+"/"+str(nb_col)+".\n"+
                  ":- dynamic signature/3.\n"+
                  ":- dynamic "+ nom_de_la_table+"/"+str(nb_col)+".\n\n"+
                  "signature("+ nom_de_la_table+","+str(maxn)+",t(\n"+
                  ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param)+")).\n\n"+
                  ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata))
    fichier0.close() 
    

for (combinaison,ind_comb) in combinaisons_list:
        nb_param = len(combinaison)
        objet_combinatoire = "forest0"
        nom_de_la_tab = gen_name_datatable(combinaison)
        for lowup in ["up","low"]:
             for maxn in range(2,taille_max_foret+1):
                    bounded = combinaison[-1]
                    dataframe_tabledata = pd.read_csv("ext_forest0/"+lowup+nom_de_la_tab+".csv")

                    valeurs_de_la_colonne_v = np.array(dataframe_tabledata["v"])
                    array_ind_entrees_egales_maxn = np.flatnonzero(valeurs_de_la_colonne_v == maxn)
                    tree_maxn = dataframe_tabledata.loc[0:max(array_ind_entrees_egales_maxn.tolist())]

                    trans_allfeaturestabledata_prolog(nom_de_la_tab,tree_maxn,lowup,maxn,bounded,nb_param,objet_combinatoire)
    
