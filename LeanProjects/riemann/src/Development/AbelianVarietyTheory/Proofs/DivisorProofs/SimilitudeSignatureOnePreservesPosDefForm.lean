import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.PositiveDefiniteFormIdentities

theorem form_pull {n : ℕ} (h Z : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) :
    star (Z *ᵥ v) ⬝ᵥ h *ᵥ (Z *ᵥ v') = star v ⬝ᵥ (Zᴴ * h * Z) *ᵥ v' := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem form_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ Q *ᵥ x = star (star x ⬝ᵥ Q *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hQ.eq, ← dotProduct_mulVec]

theorem form_expand {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (w z : Fin n → ℂ) (a : ℂ)
    (hwz : star z ⬝ᵥ Q *ᵥ w = 0) :
    star (w + a • z) ⬝ᵥ Q *ᵥ (w + a • z) =
      star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * (star z ⬝ᵥ Q *ᵥ z) := by
  have hzw : star w ⬝ᵥ Q *ᵥ z = 0 := by rw [form_swap hQ, hwz, star_zero]
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hwz, hzw, smul_eq_mul, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

theorem form_self_ofReal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x : Fin n → ℂ) :
    ((star x ⬝ᵥ Q *ᵥ x).re : ℂ) = star x ⬝ᵥ Q *ᵥ x := by
  have h := form_swap hQ x x
  exact Complex.conj_eq_iff_re.mp h.symm

end GlobalTheory.PositiveDefiniteFormIdentities

namespace GlobalTheory

open GlobalTheory.PositiveDefiniteFormIdentities in

theorem similitude_preserves_posDef : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  intro n h Q M hh Z s hdet hsig hQZ hs hsim z c hz hMz
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hQ : Q.IsHermitian := by
    rw [hQZ]
    simp [IsHermitian, conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  set q0 : ℝ := (star z ⬝ᵥ Q *ᵥ z).re with hq0
  have hq : star z ⬝ᵥ Q *ᵥ z = (q0 : ℂ) := (form_self_ofReal hQ z).symm
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  set u : Fin n → ℂ := Q *ᵥ z with hu
  set H : Matrix (Fin n) (Fin n) ℂ := ((2 / q0 : ℝ) : ℂ) • vecMulVec u (star u) - Q with hH
  have hsu : ∀ x : Fin n → ℂ, star u ⬝ᵥ x = star z ⬝ᵥ Q *ᵥ x := by
    intro x
    rw [hu, star_mulVec, ← dotProduct_mulVec, hQ.eq]
  have hus : ∀ x : Fin n → ℂ, star x ⬝ᵥ u = star (star z ⬝ᵥ Q *ᵥ x) := by
    intro x
    rw [hu, ← form_swap hQ]

  have hval : ∀ x : Fin n → ℂ, star x ⬝ᵥ H *ᵥ x =
      ((2 / q0 * Complex.normSq (star z ⬝ᵥ Q *ᵥ x) - (star x ⬝ᵥ Q *ᵥ x).re : ℝ) : ℂ) := by
    intro x
    rw [hH, sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hsu, hus, smul_eq_mul, smul_eq_mul]
    have e := form_self_ofReal hQ x
    push_cast
    rw [e, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hHh : H.IsHermitian := by
    rw [hH]
    refine IsHermitian.sub ?_ hQ
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hpos : H.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hHh fun x hx => ?_
    rw [hval x]
    refine Complex.zero_lt_real.mpr ?_
    set p := star z ⬝ᵥ Q *ᵥ x with hp
    set a : ℂ := p / (q0 : ℂ) with ha
    have hpa : p = a * q0 := by rw [ha]; field_simp
    set w := x - a • z with hw
    have hxw : x = w + a • z := by rw [hw]; abel
    have hwz : star z ⬝ᵥ Q *ᵥ w = 0 := by
      rw [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, ← hp, hpa, sub_self]
    have hexp : star x ⬝ᵥ Q *ᵥ x = star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * q0 := by
      conv_lhs => rw [hxw]
      rw [form_expand hQ w z a hwz, hq]
    have hre : (star x ⬝ᵥ Q *ᵥ x).re = (star w ⬝ᵥ Q *ᵥ w).re + Complex.normSq a * q0 := by
      rw [hexp, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnp : Complex.normSq p = Complex.normSq a * q0 ^ 2 := by
      rw [hpa, Complex.normSq_mul, Complex.normSq_ofReal]; ring
    have h2 : 2 / q0 * (Complex.normSq a * q0 ^ 2) = 2 * Complex.normSq a * q0 := by
      field_simp
    rw [hre, hnp, h2]
    by_cases hw0 : w = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        apply hx
        rw [hxw, hw0, ha0, zero_smul, add_zero]
      have e : (star w ⬝ᵥ Q *ᵥ w).re = 0 := by simp [hw0]
      rw [e]
      nlinarith [Complex.normSq_pos.mpr ha0]
    · have hZw : Zm *ᵥ w ≠ 0 := by
        intro h0
        apply hw0
        have hinv : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm = 1 := Units.inv_mul Z
        calc w = (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm) *ᵥ w := by rw [hinv, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
      have hneg := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet hsig (Zm *ᵥ z) (Zm *ᵥ w)
        (by rw [form_pull, ← hQZ]; exact hz) (by rw [form_pull, ← hQZ]; exact hwz) hZw
      rw [form_pull, ← hQZ] at hneg
      nlinarith [Complex.normSq_nonneg a]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hc : star c * c = (s : ℂ) := by
    have e1 := congrArg (fun A => star z ⬝ᵥ A *ᵥ z) hsim
    rw [← form_pull Q M z z, hMz] at e1
    simp only [star_smul, mulVec_smul, smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1
    rw [← hu, hq] at e1
    have e3 : (star c * c - s) * (q0 : ℂ) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hq0ne)
  have hMu : Mᴴ *ᵥ u = star c • u := by
    have e2 := congrArg (fun A => A *ᵥ z) hsim
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMz, mulVec_smul, mulVec_smul, smul_mulVec, ← hu] at e2
    apply smul_right_injective _ hs0
    change (s : ℂ) • (Mᴴ *ᵥ u) = (s : ℂ) • (star c • u)
    calc (s : ℂ) • (Mᴴ *ᵥ u) = star c • (c • Mᴴ *ᵥ u) := by rw [smul_smul, hc]
      _ = star c • ((s : ℂ) • u) := by rw [e2]
      _ = (s : ℂ) • (star c • u) := smul_comm _ _ _
  have hstar : star u ᵥ* M = c • star u := by
    have e : star (Mᴴ *ᵥ u) = star u ᵥ* M := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [← e, hMu, star_smul, star_star]
  have hM1 : Mᴴ * vecMulVec u (star u) * M = (s : ℂ) • vecMulVec u (star u) := by
    rw [mul_vecMulVec, vecMulVec_mul, hMu, hstar, ← hc]
    ext i j
    simp [vecMulVec_apply]
    ring
  refine ⟨H, hpos, ?_⟩
  rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM1, hsim, smul_sub,
    smul_comm ((2 / q0 : ℝ) : ℂ) (s : ℂ)]

end GlobalTheory
