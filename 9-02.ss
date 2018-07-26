#lang eopl

(require "lang-classes.ss")

(run "
class oddeven extends object
 method initialize() 1
 method even(n)
  if zero?(n) then 1 else send self odd(-(n,1))
 method odd(n)
  if zero?(n) then 0 else send self even(-(n,1))
class bogus-oddeven extends oddeven
 method even(n)
  if zero?(n) then 0 else send self odd(n)
print(send new bogus-oddeven() odd(13))")