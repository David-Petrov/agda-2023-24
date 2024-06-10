{-# OPTIONS --no-unicode #-}
module Homework.Elevator.Elevator where

open import Lib.Zero
open import Lib.Two
open import Lib.One
open import Lib.Sum

data State : Set where
  free : State
  doorsClosing : State
  moving : State

eqState : State -> State -> Two
eqState free free = tt
eqState doorsClosing doorsClosing = tt
eqState moving moving = tt
eqState _ _ = ff

data Action : State -> Set where
  gettingCalled : Action free
  targetRequestedFromInside : Action free
  forcedDoorOpening : Action doorsClosing
  successfulDoorClosing : Action doorsClosing
  arrived : Action moving

transition : (s : State) -> (a : Action s) -> State
transition free gettingCalled = doorsClosing
transition free targetRequestedFromInside = doorsClosing
transition doorsClosing forcedDoorOpening = free
transition doorsClosing successfulDoorClosing = moving
transition moving arrived = free


{-
Ще искаме `transition` да изпълнява няколко свойства, които вие ще имате за задача да формулирате и докажете.
За да изразите тези свойства, можете да използвате `eqState`, както и `Is` конструкцията.

#### Не можем да прекъсваме предвижването на асансьора
Докато асансьорът е в състояние на "предвидване към", `transition` позволява единствено той да стигне на целта си и да стане незает.

#### От незаетост единствено можем да започнем затваряне на врати
Докато асансьорът е всъстояние на "незаетост", `transition` позволява единствено той да започне да затваря вратите си.

#### Докато се затварят вратите можем да преминем единствено към незаетост или към пътуване

#### Свойство за производителност/"progress"
От каквото и да е състояние и каквото и да е действие, `transition` винаги ще промени състоянието на асансьора.
-}

elevatorUnstoppable : let s = moving in (a : Action s) -> Is (eqState free (transition s a))
elevatorUnstoppable arrived = <>

freeOnlyDoorsOpening : let s = free in (a : Action s) -> Is (eqState doorsClosing (transition s a))
freeOnlyDoorsOpening gettingCalled = <>
freeOnlyDoorsOpening targetRequestedFromInside = <>

doorsClosingOnlyFreeOrMoving : let s = doorsClosing in (a : Action s) -> Is (eqState free (transition s a) || eqState moving (transition s a))
doorsClosingOnlyFreeOrMoving forcedDoorOpening = <>
doorsClosingOnlyFreeOrMoving successfulDoorClosing = <>

transitionAlwaysProgresses : (s : State) -> (a : Action s) -> Is (not (eqState s (transition s a)))
transitionAlwaysProgresses free gettingCalled = <>
transitionAlwaysProgresses free targetRequestedFromInside = <>
transitionAlwaysProgresses doorsClosing forcedDoorOpening = <>
transitionAlwaysProgresses doorsClosing successfulDoorClosing = <>
transitionAlwaysProgresses moving arrived = <>