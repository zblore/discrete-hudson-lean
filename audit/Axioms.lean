/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson

/-!
# Axioms of the main results

Fails if any theorem of `Challenge.lean`, or either direction of the main argument, comes to
depend on anything beyond Lean's three standard axioms.
-/

/--
info: 'DiscreteHudson.wigner_im' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.wigner_im

/--
info: 'DiscreteHudson.wigner_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.wigner_eq

/--
info: 'DiscreteHudson.discrete_hudson' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.discrete_hudson

/--
info: 'DiscreteHudson.isStabilizerState_of_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.isStabilizerState_of_nonneg

/--
info: 'DiscreteHudson.wigner_nonneg_of_isStabilizerState' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.wigner_nonneg_of_isStabilizerState
