
(*
                              CS51 Lab 6
            Lazy Programming and Infinite Data Structures
                             Spring 2017
 *)


(*
                               SOLUTION
 *)


(*
Objective:

This lab provides practice with delayed (lazy) computations, both
through user code and OCaml's built in Lazy module. You will use
infinite data structures like streams and build new ones like infinite
trees.
 *)

(*====================================================================
Part 1: Programming with lazy streams

Recall the lazy stream type and associated functions from lecture,
here packaged up into a module. *)


(* The definitions here were chosen for simplicity, not for
efficiency. For instance, the definitions of first, smap, and smap2
all force their stream argument s (that is, apply it to ()) more than
once. The forces occur implicitly in the calls to head and tail. A
more efficient implementation would force only once, saving the
results. For instance,

let rec smap (f : 'a -> 'b) (s : 'a stream) : ('b stream) =
  fun () ->
    let Cons(h, t) = s() in
    Cons(f h, smap f t) ;;

Of course, in an implementation that uses memoizing thunks instead of
unit functions to delay computation, this problem of redundancy
computation is eliminated. The first force of s (whichever call it
arises from) causes the result to be cached and thereby made
immmediately available for the second force. For this reason, we'll
mostly ignore this issue of multiple forces in the solutions we give
here, though we comment on it with alternative solutions below.  *)


module LazyStream =
  struct

    type 'a str = Cons of 'a * 'a stream
     and 'a stream = unit -> 'a str ;;

    (* Extracting the head and tail of a lazy stream *)
    let head (s : 'a stream) : 'a =
      let Cons(h, _t) = s() in h ;;

    let tail (s : 'a stream) : 'a stream =
      let Cons(_h, t) = s() in t ;;

    (* Extracting the first n elements of a stream into a list *)
    let rec first (n : int) (s : 'a stream) : 'a list =
      if n = 0 then []
      else head s :: first (n - 1) (tail s) ;;

    (* Mapping a function lazily over a stream *)
    let rec smap (f : 'a -> 'b) (s : 'a stream) : ('b stream) =
      fun () -> Cons(f (head s), smap f (tail s)) ;;

    (* Mapping a binary function over two streams *)
    let rec smap2 f s1 s2 =
      fun () -> Cons(f (head s1) (head s2),
		     smap2 f (tail s1) (tail s2)) ;;
  end ;;

open LazyStream ;;

(* Here, recalled from lecture, is the definition of an infinite
   stream of ones. *)
let rec ones : int stream =
  fun () -> Cons(1, ones) ;;

(* Now you define some useful streams. Some of these were defined in
   lecture, but see if you can come up with the definitions without
   looking at the lecture slides. *)

(* An infinite stream of the integer 2. As usual, for this and all
   succeeding exercises, you shouldn't feel beholden to how the
   definition is introduced in the skeleton code below. (We'll stop
   mentioning this now, and forevermore.) *)

let rec twos =
  fun () -> Cons(2, twos) ;;


(* An infinite stream of threes, built from the ones and twos. *)
let threes =
  smap2 (+) ones twos ;;


(* An infinite stream of natural numbers (0, 1, 2, 3, ...). *)

(* Here is the implementation from lecture, which makes nats a
   recursive *value*. *)
let rec nats =
  fun () -> Cons(0, smap ((+) 1) nats) ;;

(* An alternative implementation defines a recursive *function*
   (nats_from) that generates the natural numbers starting from an
   initial value.

let rec nats_from (n : int) : int stream =
  fun () -> Cons(n, nats_from (n + 1)) ;;

let nats : int stream = nats_from 0 ;;

This approach is faster but less "inifinite data structure"-y.
 *)

(* Now some new examples. For these, don't build them directly, but
   make use of the stream mapping functions. *)

(* Infinite streams of even and odd numbers. *)
let evens = smap2 (+) nats nats ;;
let odds = smap ((+) 1) evens ;;


(* In addition to mapping over streams, we should be able to use all
   the other higher-order list functions you've grown to know and
   love, like folding and filtering. So let's implement some. *)

(* Define a function sfilter that takes a predicate (that is, a function
   returning a bool) and a stream and returns the stream that contains
   all the elements in the argument stream that satify the predicate.
   Example:

   # let evens = sfilter (fun x -> x mod 2 = 0) nats ;;
   val evens : int stream = <fun>
   # first 10 evens ;;
   - : int list = [0; 2; 4; 6; 8; 10; 12; 14; 16; 18]
 *)

(* The most straightforward way to implement filtering (though not
very efficient) is as follows: *)

let rec sfilter (pred : 'a -> bool) (s : 'a stream) : 'a stream =
  fun () ->
    if pred (head s) then Cons((head s), sfilter pred (tail s))
    else (sfilter pred (tail s)) () ;;

(* There are multiple alternatives. Perhaps you implemented one of
these. If the test of the head is moved outside the "thunk", sfilter
verifies the pred condition on the head of the stream before doing any
postponement of the tail. It thus eagerly filters out non-pred
elements, postponing only at the first pred-satisfying element. We
get:

let rec sfilter (pred : 'a -> bool) (s : 'a stream) : 'a stream =
  if pred (head s)
  then fun () -> Cons(head s, sfilter pred (tail s))
  else (sfilter pred (tail s)) ;;

This version can run much slower than the one above. Indeed, on a
stream none of whose elements satisfy p, this sfilter will never
return, because the call to sfilter in the else clause isn't postponed
at all! That problem can be remedied by delaying the else branch as
well:

let rec sfilter (pred : 'a -> bool) (s : 'a stream) : 'a stream =
  if pred (head s)
  then fun () -> Cons(head s, sfilter pred (tail s))
  else fun () -> (sfilter pred (tail s)) () ;;

All of these implementations so far implicitly force evalution of s
(that is, apply s to ()) multiple times by virtue of the multiple
calls to head and tail, each of which forces s. (This is the same
issue mentioned above in the discussion of smap.) To remove this
expensive recomputation, we can force s explicitly once and reuse the
results.

let rec sfilter pred s =
  let Cons(h, t) = s() in
  if pred h then fun () -> Cons(h, sfilter pred t)
  else fun () -> (sfilter pred t) () ;;
 *)


(* Now redefine evens and odds using sfilter *)

let even x = (x mod 2) = 0 ;;
let odd x = not (even x) ;;

let evens2 = sfilter even nats ;;
let odds2 = sfilter odd nats ;;

(*====================================================================
Part 2: Eratosthenes Sieve

Eratosthenes sieve is a method for generating the prime numbers. Given
a list of natural numbers starting with 2, we filter out those in the
tail of the list not divisible by the first element of the list and
apply the sieve to that tail. The first few steps go something like
this: We start with the natural numbers (in the example here, just a
prefix of them).

2 3 4 5 6 7 8 9 10 11 12 13 14 15

The first element, 2, is prime. Now we remove numbers divisible by 2
from the tail of the list (marking here with a | the boundary between
the first element and the tail we're currently working on:

2  |  3 5 7 9 11 13 15

and apply the sieve to the tail:

2 3  |  5 7 11 13

and again:

2 3 5  |  7 11 13
2 3 5 7  |  11 13
...
2 3 5 7 11 13

Implement Eratosthenes sieve to generate an infinite stream of primes.
Example:

# primes = sieve (tail (tail nats)) ;;
# first 4 primes ;;
- : int list = [2; 3; 5; 7]

You probably won't want to generate more than the first four primes
this way; it'll take too long. Here are some timings from the solution
code on my laptop:

  n      time for first n primes (seconds)
  1 --   0.0000
  2 --   0.0002
  3 --   0.0020
  4 --   0.0980
  5 --   0.9296
  6 --  50.6515

You'll address that problem next. *)

let not_div_by n m =
    not (m mod n = 0) ;;

(* The idea in implementing sieve is as follows:

   1. Retrieve the head and tail of the stream. The head is the first
      prime in the stream, the tail the list of remaining elements
      that have not been sieved yet. For instance,

      head      | tail
      2         | 3 4 5 6 7 8 9 10 11 ...

   2. Filter out all multiples of the head from the tail.

      head      | filtered tail
      2         | 3 5 7 9 11 ...

   3. Sieve the tail to generate all primes starting with the first
      element of the tail.

      head      | sieved filterd tail
      2         | 3 5 7 11 ...

   4. Add the head on the front of the sieved results.

      2 3 5 7 11 ...

   5. Of course, this whole series of computations should be delayed,
      and only executed when forced to do so.

A direct implementation of this idea (with numbers keyed to the
description above) would be:

let rec sieve s =
  fun () -> Cons(head s,
		 sieve (sfilter (not_div_by (head s)) (tail s))) ;;
    ^         ^    ^       ^                     ^         ^
    |         |    |       |                     |         |
    5         4    3       2                     1         1

But as in sfilter above this forces s multiple times. Instead, we can
force once and save the results: *)

(*
let rec sieve s =
  fun () ->
    let Cons(h, t) = s() in
    Cons(h, sieve (sfilter (not_div_by h) t)) ;;
 *)

let rec sieve (s : int stream) : int stream =
  let Cons(h, t) = s() in
  fun () -> Cons(h, sieve (sfilter (not_div_by h) t)) ;;

let primes : int stream = sieve (tail (tail nats)) ;;

(* We generate a table of some times to generate primes: *)

exception Done ;;

let _ =
  try
    print_endline "Testing sieve based on lazy streams";
    for n = 1 to 100 do
      let _l, t = CS51.call_timed (first n) primes in
      Printf.printf "%3d -- %12.8f\n" n t;
      if t > 0.5 then raise Done
    done
  with Done -> () ;;

(*====================================================================
Part 3: Using OCaml's Lazy module

All of the recomputation going on behind the scenes with these
stream-based solutions is prohibitive. In lecture we described the use
of *memoizing* to eliminate the recomputation, and showed an
implementation in terms of refs. That functionality is actually
already available in OCaml through its Lazy module. The module
introduces a new type -- 'a Lazy.t -- of delayed elements of type 'a,
and a new function Lazy.force : 'a Lazy.t -> 'a that forces a delayed
computation to occur, saving the result if this is the first time the
value was forced and simply returning the saved value on later
requests. For instance, suppose we've defined the Fibonacci function
naively as *)

let rec fib (n : int) : int =
  if n < 2 then n
  else (fib (n - 1)) + (fib (n - 2)) ;;

(* Then a delayed computation of the 42nd Fibonacci number would be *)

let fib42 : int Lazy.t =
  lazy (fib 42) ;;

(* Here, we force the computation twice in a row, timing the two calls:

# CS51.call_reporting_time Lazy.force fib42 ;;
Elapsed time: 13.380860
- : int = 267914296
# CS51.call_reporting_time Lazy.force fib42 ;;
Elapsed time: 0.000000
- : int = 267914296

The first time through takes 13 seconds, the second less than a
microsecond.

Below is an incomplete reimplementation of the LazyStreams module
above using the OCaml Lazy module. Complete this implementation by
implementing smap, smap2, and sfilter. *)

module NativeLazyStreams =
  struct

    type 'a str = Cons of 'a * 'a stream
     and 'a stream = 'a str Lazy.t ;;

    let head (s : 'a stream) : 'a =
      let Cons(h, _t) = Lazy.force s in h ;;

    let tail (s : 'a stream) : 'a stream =
      let Cons(_h, t) = Lazy.force s in t ;;

    let rec first (n : int) (s : 'a stream) : 'a list =
      if n = 0 then []
      else head s :: first (n - 1) (tail s) ;;

    let rec smap (f : 'a -> 'b) (s : 'a stream) : 'b stream =
      lazy (Cons(f (head s), smap f (tail s)));;


    let rec smap2 (f : 'a -> 'b -> 'c)
                  (s1 : 'a stream)
                  (s2 : 'b stream)
                  : 'c stream =
      lazy (Cons(f (head s1) (head s2), smap2 f (tail s1) (tail s2))) ;;


    let rec sfilter (pred : 'a -> bool) (s : 'a stream) : 'a stream =
      lazy (if pred (head s)
	    then Cons((head s), sfilter pred (tail s))
	    else Lazy.force (sfilter pred (tail s))) ;;

  end

(* Now we can redo the Fibonacci example. *)
open NativeLazyStreams ;;

let rec fibs =
  lazy (Cons(0, lazy (Cons(1, smap2 (+) fibs (tail fibs))))) ;;

(* This version is much faster, even the first time around. Why?

# CS51.call_reporting_time (first 50) fibs ;;
time (msecs): 0.029087
- : int list =
[0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610; 987; 1597;
 2584; 4181; 6765; 10946; 17711; 28657; 46368; 75025; 121393; 196418; 317811;
 514229; 832040; 1346269; 2178309; 3524578; 5702887; 9227465; 14930352;
 24157817; 39088169; 63245986; 102334155; 165580141; 267914296; 433494437;
 701408733; 1134903170; 1836311903; 2971215073; 4807526976; 7778742049]
# CS51.call_reporting_time (first 50) fibs ;;
time (msecs): 0.006914
- : int list =
[0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610; 987; 1597;
 2584; 4181; 6765; 10946; 17711; 28657; 46368; 75025; 121393; 196418; 317811;
 514229; 832040; 1346269; 2178309; 3524578; 5702887; 9227465; 14930352;
 24157817; 39088169; 63245986; 102334155; 165580141; 267914296; 433494437;
 701408733; 1134903170; 1836311903; 2971215073; 4807526976; 7778742049]
 *)

(* Redo the Eratosthenes sieve using the NativeLazyStreams by
   completing the functions below. *)

let rec nats2 =
  lazy (Cons(0, smap ((+) 1) nats2)) ;;

let rec sieve2 s =
  lazy (Cons(head s, sieve2 (sfilter (not_div_by (head s)) (tail s)))) ;;

let primes2 = sieve2 (tail (tail nats2)) ;;

(* How much further can you get computing primes now that the
   recomputation problem is solved?  Implement a function to find the
   nth element in a stream, and use it to find out the 2000th
   prime. *)

let rec nth (s : 'a stream) (n : int) : 'a =
  if n = 0 then head s
  else nth (tail s) (n - 1) ;;

(* Here's the same table now with the new sieve: *)
let _ =
  try
    print_endline "Testing sieve based on native lazy streams";
    for n = 1 to 100 do
      let _l, t = CS51.call_timed (first n) primes2 in
      Printf.printf "%3d -- %12.8f\n" n t;
      if t > 0.5 then raise Done
    done
  with Done -> () ;;
