import OMAStatements.S_oeis_a176753
import Mathlib

/-!
Mathar's recurrence follows by formally differentiating the quadratic
generating equation. Clearing its linear denominator gives an equation
for the square of `1 - 2*X*G`, so the square root stays implicit.
-/

namespace A176753Bridge

open Finset PowerSeries
open OMA.S_oeis_a176753 (a aList)

private theorem prefix_length : ∀ n : ℕ, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [aList, List.length_append, prefix_length (n + 1)]
      rfl

private theorem prefix_step {n i : ℕ} (hi : i ≤ n) :
    (aList (n + 1)).getD i 0 = (aList n).getD i 0 := by
  cases n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n =>
      rw [aList, List.getD_append]
      rw [prefix_length]
      omega

private theorem prefix_agrees {i n : ℕ} (hi : i ≤ n) : (aList n).getD i 0 = a i := by
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases hn : i ≤ n
      · exact (prefix_step hn).trans (ih hn)
      · have : i = n + 1 := by omega
        subst i
        rfl

theorem a_convolution (n : ℕ) :
    a (n + 2) = (∑ i ∈ range (n + 2), a i * a (n + 1 - i)) - 2 := by
  change (aList (n + 2)).getD (n + 2) 0 = _
  have hlen : (aList (n + 1)).length = n + 2 := prefix_length _
  rw [aList, List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self]
  change (∑ i ∈ range (n + 2), (aList (n + 1)).getD i 0 *
    (aList (n + 1)).getD (n + 1 - i) 0) - 2 = _
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [prefix_agrees (by have := mem_range.mp hi; omega), prefix_agrees (Nat.sub_le _ _)]

private abbrev G : PowerSeries ℤ := PowerSeries.mk a

private theorem coeff_square (n : ℕ) : coeff n (G ^ 2) = ∑ i ∈ range (n + 1), a i * a (n - i) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]

private theorem coeff_tail (n : ℕ) :
    coeff n ((X : PowerSeries ℤ)^2 * PowerSeries.mk 1) = if 2 ≤ n then 1 else 0 := by
  rw [coeff_X_pow_mul']
  simp

private theorem generating_unmultiplied :
    G = 1 + X * G ^ 2 - C (2 : ℤ) * ((X : PowerSeries ℤ)^2 * PowerSeries.mk 1) := by
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, coeff_mk, coeff_C_mul, coeff_tail]
  rcases n with _ | _ | n
  · simp [a, aList]
  · simp [coeff_square, a, aList, show ¬ 2 ≤ (1 : ℕ) by decide]
  · simpa only [coeff_one, Nat.succ_ne_zero, if_false, Nat.le_add_left, if_true,
      coeff_succ_X_mul, coeff_square, two_mul, mul_one, zero_add] using a_convolution n

/-- The algebraic equation for the exact integer generating series. -/
theorem generating_bridge :
    let G : PowerSeries ℤ := PowerSeries.mk a
    let B : PowerSeries ℤ := 1 - X
    B * G = B + X * B * G ^ 2 - 2 * X ^ 2 := by
  dsimp only
  let B : PowerSeries ℤ := 1 - X
  change B * G = B + X * B * G ^ 2 - 2 * X ^ 2
  have hgeo : (PowerSeries.mk 1 : PowerSeries ℤ) * B = 1 := mk_one_mul_one_sub_eq_one ℤ
  have htwo : C (2 : ℤ) = (2 : PowerSeries ℤ) := map_ofNat _ _
  calc
    B * G = B * (1 + X * G ^ 2 - C (2 : ℤ) * ((X : PowerSeries ℤ)^2 * PowerSeries.mk 1)) :=
      congrArg (B * ·) generating_unmultiplied
    _ = B + X * B * G ^ 2 - 2 * X ^ 2 * ((PowerSeries.mk 1 : PowerSeries ℤ) * B) := by
      rw [htwo]
      ring
    _ = _ := by rw [hgeo, mul_one]

end A176753Bridge

open PowerSeries

namespace A176753Differential

private abbrev Series := PowerSeries ℤ
private noncomputable abbrev Xz : Series := PowerSeries.X
private noncomputable abbrev der := PowerSeries.derivative ℤ

private theorem differentialEquation (G : Series)
    (hG : (1 - Xz) * G = (1 - Xz) + Xz * (1 - Xz) * G ^ 2 - 2 * Xz ^ 2) :
    4 * ((1 - 6 * Xz + 9 * Xz ^ 2 + 4 * Xz ^ 3 - 8 * Xz ^ 4) * (Xz * der G) +
      (1 - 4 * Xz + 5 * Xz ^ 2 - 6 * Xz ^ 3) * G) =
      -(-4 + 8 * Xz + 20 * Xz ^ 2 - 16 * Xz ^ 3) := by
  let B : Series := 1 - Xz
  let P : Series := 1 - 5 * Xz + 4 * Xz ^ 2 + 8 * Xz ^ 3
  let U : Series := 1 - 2 * Xz * G
  have hsq : B * U ^ 2 = P := by
    dsimp [B, U, P]
    linear_combination (-4 * Xz) * hG
  have hdB : der B = -1 := by simp [B]
  have dNum (n : ℕ) : der (n : Series) = 0 := Derivation.map_natCast _ n
  have d2 : der (2 : Series) = 0 := by simpa only [Nat.cast_ofNat] using dNum 2
  have d4 : der (4 : Series) = 0 := by simpa only [Nat.cast_ofNat] using dNum 4
  have d5 : der (5 : Series) = 0 := by simpa only [Nat.cast_ofNat] using dNum 5
  have d8 : der (8 : Series) = 0 := by simpa only [Nat.cast_ofNat] using dNum 8
  have hdP : der P = -5 + 8 * Xz + 24 * Xz ^ 2 := by
    simp [P, Derivation.leibniz, smul_eq_mul, d4, d5, d8]
    ring
  have hdU : der U = -(2 * G + 2 * Xz * der G) := by
    simp [U, Derivation.leibniz, smul_eq_mul, d2]
    ring
  have hderivative : -(U ^ 2) + 2 * B * U * der U = der P := by
    have h := congrArg (fun F : Series => der F) hsq
    simp only [Derivation.leibniz, PowerSeries.derivative_pow, hdB, smul_eq_mul] at h
    norm_num at h
    linear_combination h
  have hproduct : 2 * B * P * der U = (B * der P + P) * U := by
    linear_combination (B * U) * hderivative - (2 * B * der U - U) * hsq
  let Q : Series := B * P
  let R : Series := B * der P + P
  let S : Series := 1 - 4 * Xz + 5 * Xz ^ 2 - 6 * Xz ^ 3
  have hQ : Q = 1 - 6 * Xz + 9 * Xz ^ 2 + 4 * Xz ^ 3 - 8 * Xz ^ 4 := by
    dsimp [Q, B, P]
    ring
  have hR : R = -4 + 8 * Xz + 20 * Xz ^ 2 - 16 * Xz ^ 3 := by
    change B * der P + P = _
    rw [hdP]
    dsimp [B, P]
    ring
  have hS : 2 * Q - Xz * R = 2 * S := by rw [hQ, hR]; dsimp [S]; ring
  have hpolynomial : 2 * Q * (-(2 * G + 2 * Xz * der G)) = R * (1 - 2 * Xz * G) := by
    rw [hdU] at hproduct
    simpa only [Q, R, mul_assoc, U] using hproduct
  have hfinal : 4 * (Q * (Xz * der G) + S * G) = -R := by
    linear_combination -hpolynomial - (2 * G) * hS
  rw [hQ, hR] at hfinal
  exact hfinal

private lemma coeffShift (f : Series) (n j : ℕ) (hj : j ≤ n) :
    coeff n (Xz ^ j * f) = coeff (n - j) f := by
  simpa only [Nat.sub_add_cancel hj] using
    (PowerSeries.coeff_X_pow_mul f j (n - j))

private lemma coeffNumeralMul (n k : ℕ) [k.AtLeastTwo] (f : Series) :
    coeff n ((OfNat.ofNat k : Series) * f) = (OfNat.ofNat k : ℤ) * coeff n f := by
  have hc : PowerSeries.C (OfNat.ofNat k : ℤ) = (OfNat.ofNat k : Series) := map_ofNat _ _
  rw [← hc, PowerSeries.coeff_C_mul]

private lemma coeffEuler (G : Series) (n : ℕ) :
    coeff n (Xz * der G) = (n : ℤ) * coeff n G := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    have h := PowerSeries.coeff_X_pow_mul (der G) 1 n
    rw [pow_one, PowerSeries.coeff_derivative] at h
    simpa only [Nat.cast_succ, mul_comm, Nat.succ_eq_add_one] using h

private theorem coeffRecurrence (G : Series)
    (hG : (1 - Xz) * G = (1 - Xz) + Xz * (1 - Xz) * G ^ 2 - 2 * Xz ^ 2)
    (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * coeff n G
      + 2 * (1 - 3 * (n : ℤ)) * coeff (n - 1) G
      + (9 * (n : ℤ) - 13) * coeff (n - 2) G
      + 2 * (2 * (n : ℤ) - 9) * coeff (n - 3) G
      + 8 * (4 - (n : ℤ)) * coeff (n - 4) G = 0 := by
  have hk (k : ℕ) (h : k ≤ 4) : k ≤ n := h.trans hn
  have hs (f : Series) : coeff n (Xz * f) = coeff (n - 1) f := by
    simpa only [pow_one] using coeffShift f n 1 (hk 1 (by decide))
  have hQ (f : Series) :
      coeff n ((1 - 6 * Xz + 9 * Xz ^ 2 + 4 * Xz ^ 3 - 8 * Xz ^ 4) * f) =
        coeff n f - 6 * coeff (n - 1) f + 9 * coeff (n - 2) f +
          4 * coeff (n - 3) f - 8 * coeff (n - 4) f := by
    simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add]
    rw [coeffNumeralMul n 6, coeffNumeralMul n 9, coeffNumeralMul n 4, coeffNumeralMul n 8,
      hs f, coeffShift f n 2 (hk 2 (by decide)), coeffShift f n 3 (hk 3 (by decide)),
      coeffShift f n 4 hn]
  have hS :
      coeff n ((1 - 4 * Xz + 5 * Xz ^ 2 - 6 * Xz ^ 3) * G) =
        coeff n G - 4 * coeff (n - 1) G + 5 * coeff (n - 2) G -
          6 * coeff (n - 3) G := by
    simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add]
    rw [coeffNumeralMul n 4, coeffNumeralMul n 5, coeffNumeralMul n 6, hs G,
      coeffShift G n 2 (hk 2 (by decide)), coeffShift G n 3 (hk 3 (by decide))]
  have hr₀ : coeff n (4 : Series) = 0 := by
    have h := coeffNumeralMul n 4 (1 : Series)
    simpa [PowerSeries.coeff_one, show n ≠ 0 by omega] using h
  have hr :
      coeff n (-(-4 + 8 * Xz + 20 * Xz ^ 2 - 16 * Xz ^ 3)) = 0 := by
    rw [map_neg, map_sub, map_add, map_add, map_neg, hr₀,
      coeffNumeralMul n 8, coeffNumeralMul n 20, coeffNumeralMul n 16]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega]
  have heq := congrArg (fun f : Series => coeff n f) (differentialEquation G hG)
  rw [coeffNumeralMul n 4, map_add, hQ, hS, hr] at heq
  simp only [coeffEuler, Nat.cast_sub (hk 1 (by decide)), Nat.cast_sub (hk 2 (by decide)),
    Nat.cast_sub (hk 3 (by decide)), Nat.cast_sub hn] at heq
  apply (mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0))
  rw [mul_zero]
  linear_combination heq

end A176753Differential

theorem OMA.solution : type_of% @OMA.S_oeis_a176753.main := by
  intro n hn
  simpa only [PowerSeries.coeff_mk] using
    A176753Differential.coeffRecurrence (PowerSeries.mk OMA.S_oeis_a176753.a)
      A176753Bridge.generating_bridge n hn
