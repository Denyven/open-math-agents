import Mathlib

/-!
# Maximal correlation with one Gaussian marginal

Source: https://mathoverflow.net/questions/228204

The Pearson coefficient is defined for nondegenerate variables of finite
variance, so the coordinates are centered and scaled to variance one.
Borel transforms are closed under the inverse affine maps used here.
After this normalization the Gaussian marginal is standard normal.

The criterion uses a finite Borel partition of each marginal at a time.
A pair of simple functions specifies its cell values. The resulting
inequality is equivalent to positive semidefiniteness of the block matrix
with the two marginal covariance matrices on the diagonal, scaled by the
absolute Pearson coefficient, and the cross covariance matrix off-diagonal.
Exact equality at positive correlation with a non-Gaussian marginal
refutes the proposed Gaussian stability.
-/

namespace OMA.S_mo_228204

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal

universe u

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The product moment, which equals Pearson correlation for standardized variables. -/
noncomputable def cross (P : Measure Ω) (u v : Ω → ℝ) : ℝ :=
  ∫ x, u x * v x ∂P

noncomputable def cov (P : Measure Ω) (u v : Ω → ℝ) : ℝ :=
  cross P u v - (∫ x, u x ∂P) * (∫ x, v x ∂P)

def Standard (P : Measure Ω) (u : Ω → ℝ) : Prop :=
  Measurable u ∧ Integrable (fun x => u x ^ 2) P ∧
    (∫ x, u x ∂P) = 0 ∧ (∫ x, u x ^ 2 ∂P) = 1

def attainable (P : Measure Ω) (X Y : Ω → ℝ) : Set ℝ :=
  {r | ∃ f g : ℝ → ℝ, Measurable f ∧ Measurable g ∧
    Standard P (f ∘ X) ∧ Standard P (g ∘ Y) ∧ r = |cross P (f ∘ X) (g ∘ Y)|}

/-- HGR maximal correlation. The absolute value is equivalent by sign symmetry. -/
noncomputable def maximal (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  sSup (attainable P X Y)

/-- The positive semidefiniteness tests for all finite Borel probability tables. -/
def FiniteTableTest (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ f g : SimpleFunc ℝ ℝ,
    2 * |cov P (f ∘ X) (g ∘ Y)| ≤
      |cross P X Y| * (cov P (f ∘ X) (f ∘ X) + cov P (g ∘ Y) (g ∘ Y))

/-- One independent fair coin and two independent standard Gaussian coordinates. -/
abbrev Sample := Bool × (ℝ × ℝ)

def PositiveCounterexample : Prop :=
  ∃ (P : Measure Sample) (X Y : Sample → ℝ),
    IsProbabilityMeasure P ∧ Standard P X ∧ Standard P Y ∧
    P.map Y = gaussianReal 0 1 ∧ P.map X ≪ volume ∧
    (∀ (m : ℝ) (v : ℝ≥0), P.map X ≠ gaussianReal m v) ∧
    0 < cross P X Y ∧ maximal P X Y ^ 2 = cross P X Y ^ 2

theorem main :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ), Standard P X → Standard P Y → P.map X ≪ volume →
      P.map Y = gaussianReal 0 1 →
      (maximal P X Y ^ 2 = cross P X Y ^ 2 ↔ FiniteTableTest P X Y)) ∧
    PositiveCounterexample := by
  sorry

end OMA.S_mo_228204
