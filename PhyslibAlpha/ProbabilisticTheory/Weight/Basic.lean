/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Basic
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual

/-!
# Weights

Weights: additive, possibly infinite maps on the positive cone; states are finite normalized ones.

## i. Overview

A state assigns each positive observable a nonnegative expectation value, normalized so the certain
outcome reads exactly `1`. A weight drops the normalization and allows the value `+∞`. This matters
in infinite dimensions: the trace on `B(H)` is finite only on the trace-class operators. A state is
a weight that is finite and normalized.

## ii. Key results

- `Weight.mono` : weights are monotone on the positive cone.
- `Weight.IsFinite.isSemifinite` : a finite weight is automatically semifinite.
- `Weight.IsFinite.normalize_isState` : rescaling a finite weight that's nonzero at the order unit
  turns it into a state.

## iii. Table of contents

- A. Weights
- B. States as weights

## iv. References

- G. Ludwig, *Foundations of Quantum Mechanics I*, Springer, 1983.
  <https://link.springer.com/book/10.1007/978-3-642-86751-4>

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ENNReal NNReal

/-!

## A. Weights

-/

/-- An extended nonnegative linear functional on the positive cone. -/
abbrev Weight (E : Type*) [OrderedVectorSpace E] := _root_.Weight E

namespace Weight

section OrderedVectorSpace

variable {E : Type*} [OrderedVectorSpace E]

export _root_.Weight
  (IsFaithful IsFinite IsSemifinite IsNormal monotone toReal_map_nnreal_smul)

@[ext]
lemma ext {w₁ w₂ : Weight E} (h : ∀ A, w₁ A = w₂ A) : w₁ = w₂ :=
  LinearMap.ext h

/-- Weights are monotone on the positive cone. -/
lemma mono (w : Weight E) : Monotone (w : PosCone E → ℝ≥0∞) :=
  w.monotone

namespace IsFinite

export _root_.Weight.IsFinite (isSemifinite toReal_map_add)

end IsFinite

end OrderedVectorSpace

/-!

## B. States as weights

-/

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

export _root_.Weight (IsState normalize normalize_apply)

namespace IsFinite

export _root_.Weight.IsFinite (normalize_isFinite normalize_isState)

end IsFinite

end OrderUnitSpace

end Weight

end ProbabilisticTheory
