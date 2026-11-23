import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate
attribute [local instance] IsCMField.starRing

namespace GlobalTheory.SelfDualDet
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy GlobalTheory.LocalLattice

theorem congr_of_hasSignature {r p q : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ Bᵀ = Qᵀ * Aᵀ * Q.map conj := by
  obtain ⟨e, P, hP⟩ := hA
  obtain ⟨f, R, hR⟩ := hB
  have hc : ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ :=
    fun _ => rfl
  rw [hc] at hP hR
  have h1 : Matrix.reindex f f B = (P * R⁻¹).1ᴴ * Matrix.reindex e e A * (P * R⁻¹).1 := by
    have h2 : (R⁻¹).1ᴴ * R.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    calc Matrix.reindex f f B = ((R⁻¹).1ᴴ * R.1ᴴ) * Matrix.reindex f f B * (R.1 * (R⁻¹).1) := by
          rw [h2, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹).1ᴴ * (R.1ᴴ * Matrix.reindex f f B * R.1) * (R⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hR, ← hP, Units.val_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  generalize P * R⁻¹ = S at h1
  refine ⟨S.1.submatrix e f, ?_, ?_⟩
  · refine (Matrix.isUnit_det_of_right_inverse (B := (S⁻¹).1.submatrix f e) ?_).ne_zero
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  · have h3 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) h1
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h3
    rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
      Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] at h3
    exact h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_eq_of_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r r' : ℕ} (h : r = r')
    {G : Matrix (Fin r) (Fin r) E} {G' : Matrix (Fin r') (Fin r') E}
    (hG : ∀ a b, cc (Gᵀ a b) = Gᵀ b a) (hG' : ∀ a b, cc (G'ᵀ a b) = G'ᵀ b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} {L' : Submodule (𝓞 E) (Fin r' → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) :
    ∃ z : E, G'.det = z * star z * G.det := by
  subst h
  obtain ⟨P, -, hP⟩ := congr_of_modular (E := E) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd')
    fun τ => by
      obtain ⟨p, q, h1, h2⟩ := hs τ
      exact congr_of_hasSignature h1 h2
  have h1 := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_transpose,
    Published.det_map_cc] at h1
  refine ⟨P.det, h1.trans ?_⟩
  change _ = _ * cc _ * _
  ring

theorem det_eq_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  intro E _ _ _ hc W₁ W₂ h₁ h₂ hr hs
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  exact det_eq_of_matrix hr (fun a b => W₁.herm.eq (W₁.frame b) (W₁.frame a))
    (fun a b => W₂.herm.eq (W₂.frame b) (W₂.frame a))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₂).ne_zero
    (isLattice_coordLat W₁ W₁.L0 W₁.standardTuple_isLattice) (isLattice_coordLat W₂ W₂.L0 W₂.standardTuple_isLattice)
    (selfDual_coordLat W₁ W₁.L0 W₁.baseLattice_isUnimodular) (selfDual_coordLat W₂ W₂.L0 W₂.baseLattice_isUnimodular)
    fun τ => ⟨_, _, h₁ τ, hs τ ▸ h₂ τ⟩

end GlobalTheory.SelfDualDet
