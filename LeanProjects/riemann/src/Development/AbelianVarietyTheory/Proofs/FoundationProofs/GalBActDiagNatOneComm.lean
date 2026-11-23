import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem toGQ_diag_nat_one_ent (q : ℕ) (hq : 0 < q) :
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 0 = (q : ℚ) ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 1 = 0 ∧
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 0 = 0 ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 1 = 1 := by
  have h : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; omega
  unfold ent toGQ
  rw [dif_pos h]
  simp

theorem eOm_zero_of_injective_diag {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (hε : Function.Injective ε) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun hε 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.exp_sl_diag_coeff (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f)).coeff r = (X.exp f).coeff (r / q) := by
  obtain ⟨h00, h01, h10, h11⟩ := toGQ_diag_nat_one_ent q hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := X.exp_upper _ h10 f (r / q)
  rw [h00, h01, h11, mul_zero, zero_div, eOm_zero_of_injective_diag ε hε, one_mul, div_one, div_mul_cancel₀ r hqQ] at h
  exact h

theorem Tower.gal_sl_diag (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.gal s f) := by
  apply RingHom.injective X.exp.toRingHom
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, X.exp_sl_diag_coeff hε q hq, X.exp_sl_diag_coeff hε q hq, X.gal_exp]

theorem mZl_diag_nat_one_mulVec (l : ℕ) [Fact l.Prime] (q : ℕ) (c : ℤ_[l]) (u : Fin 2 → ℤ_[l]) :
    mZl l !![(q : ℤ), 0; 0, 1] *ᵥ ![u 0, c * u 1] =
      ![(mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 0, c * (mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 1] := by
  funext i
  fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tower.galB_act_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l),
      X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  intro Ω _ _ ε X hε l _ q hq s b
  funext u
  simp only [Tower.galB, Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, Tower.kmap_kmap, mZl_diag_nat_one_mulVec]
  have hφ : (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv.trans (X.gal s) =
      (X.gal s).trans (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv :=
    RingEquiv.ext fun f => X.gal_sl_diag hε q hq s f
  rw [hφ]

end GlobalTheory.KZ
