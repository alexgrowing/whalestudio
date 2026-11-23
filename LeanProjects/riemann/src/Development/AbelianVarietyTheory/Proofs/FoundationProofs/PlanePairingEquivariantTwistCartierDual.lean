import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem tbA_eps_mul (c : Coef l) (n : ℕ) (s : G ℚ Ω) (u : Qn c n) :
    tbA c n (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * u) =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * tbA c n u := by
  obtain ⟨x, rfl⟩ := red_surjective c n u
  have h : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  have e : (⟨eps l s, CupCob.eps_mem c s⟩ : c.O) * x = ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) • x := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, Algebra.smul_def, ← h]
  rw [← map_mul, e, tbA_red, tbA_red, map_smul, smul_eq_mul, map_mul]
  rfl

theorem matQ_dual1_apply (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) (i j : Fin 2) :
    matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s i j =
      red c n ⟨eps l s, CupCob.eps_mem c s⟩ *
        (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) *
        matQ c n W hint s i j := by
  simp only [matQ_apply, ← map_mul, ← map_sub]
  congr 1
  apply Subtype.ext
  show mat (dual1 W) s i j = eps l s * (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) * mat W s i j
  rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]

theorem matQ_det_sq (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) :
    (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) ^ 2 = 1 := by
  simp only [matQ_apply, ← map_mul, ← map_sub, ← map_pow]
  rw [← map_one (red c n)]
  congr 1
  apply Subtype.ext
  show (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) ^ 2 = 1
  rw [← Matrix.det_fin_two]
  exact CupCob.det_sq W hdet s

end GlobalTheory.Ord2.SelPerp

theorem GlobalTheory.Ord2.SelPerp.Phi_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  intro l _ Ω _ _ c n W hint hdet S hN μ hμ s y
  refine TDual.ext fun x => ?_
  have hμs : μ (toGS Ω (S : Set Pl) s) = cycMod ℚ Ω l n s := by rw [← hμ]; rfl
  obtain ⟨p, rfl⟩ : ∃ p : Mn c n, x = matQ c n W hint s *ᵥ p :=
    ⟨matQ c n W hint s⁻¹ *ᵥ x, by
      rw [Matrix.mulVec_mulVec, ← matQ_mul, mul_inv_cancel, matQ_one, Matrix.one_mulVec]⟩
  rw [twDual_apply, ← map_inv, rhoS_toGS, Matrix.mulVec_mulVec, ← matQ_mul, inv_mul_cancel, matQ_one,
    Matrix.one_mulVec, hμs, SelPerp.Phi_apply, SelPerp.Phi_apply, ← SelPerp.tbA_eps_mul]
  congr 1
  have hd := SelPerp.matQ_det_sq c n W hint hdet s
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, SelPerp.matQ_dual1_apply c n W hint hdet]
  linear_combination (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * (p 0 * y 1 - p 1 * y 0)) * hd
