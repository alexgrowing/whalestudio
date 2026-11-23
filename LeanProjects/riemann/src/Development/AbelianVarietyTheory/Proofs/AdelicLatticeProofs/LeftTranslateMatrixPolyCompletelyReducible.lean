import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepresStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStableStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTransposeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormPropertiesStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem ltr_mul_left {ι : Type} [Fintype ι] [DecidableEq ι] (g h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ltr (g * h) f = ltr h (ltr g f) := by
  have : ltr (g * h) = (ltr h).comp (ltr g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [ltr, MvPolynomial.aeval_X, AlgHom.comp_apply, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [this]; rfl

theorem ltr_one_left {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℂ) :
    ltr (1 : Matrix ι ι ℂ) f = f := by
  have : ltr (1 : Matrix ι ι ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [ltr, MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Matrix.one_apply_ne hb.symm]
    · simp
  rw [this]; rfl

noncomputable def ltrRep {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] (ρ : G →* Matrix ι ι ℂ) :
    Representation ℂ G (MvPolynomial (ι × ι) ℂ) where
  toFun g := (ltr (ρ g⁻¹)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    simp [ltr_one_left]
  map_mul' g h := by
    refine LinearMap.ext fun f => ?_
    simp [ltr_mul_left]

noncomputable def dualPowRep {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] (ρ : G →* Matrix ι ι ℂ) (n : ℕ) :
    Representation ℂ G ((Fin n → ι) → ℂ) where
  toFun g := Matrix.toLin' (tpow n (ρ g⁻¹))ᵀ
  map_one' := by
    rw [inv_one, map_one, ((GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).1 n).1, transpose_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [_root_.mul_inv_rev, map_mul, ((GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).1 n).2.1, transpose_mul, Matrix.toLin'_mul]; rfl

theorem ltr_completely_reducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ U : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U, ltr g f ∈ U) → ∃ U' : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U', ltr g f ∈ U') ∧ IsCompl U U' := by
  intro ι _ _ Γ hΓ hss U hU
  obtain ⟨G, _, ρ, hρ⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  have hs : ∀ n, (dualPowRep ρ n).IsSemisimpleRepresentation := by
    intro n
    rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin n → ι) G _ (dualPowRep ρ n) (Pi.basisFun ℂ _)]
    have h := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hΓ hss n
    convert h using 1
    subst hρ
    ext M
    simp only [Set.mem_range, Set.mem_image, LinearMap.toMatrix_eq_toMatrix']
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ρ g⁻¹, ⟨_, rfl⟩, (LinearMap.toMatrix'_toLin' _).symm⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      change LinearMap.toMatrix' (Matrix.toLin' (tpow n (ρ g⁻¹⁻¹))ᵀ) = _
      rw [inv_inv, LinearMap.toMatrix'_toLin']
  choose p _ hp2 hp3 using (GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι).2.2.2
  have hsemi : (ltrRep ρ).IsSemisimpleRepresentation := by
    refine GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant G _ (ltrRep ρ) (Σ n : ℕ, (Fin n → ι)) (fun j => (Fin j.1 → ι) → ℂ)
      (fun j => dualPowRep ρ j.1) (fun j => p j.1 j.2) (fun j => hs j.1) ?_ ?_
    · rintro ⟨n, b⟩ g v
      change p n b (Matrix.toLin' (tpow n (ρ g⁻¹))ᵀ v) = ltr (ρ g⁻¹) (p n b v)
      rw [hp2, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    · rw [eq_top_iff]
      intro f _
      rw [← MvPolynomial.sum_homogeneousComponent f]
      refine Submodule.sum_mem _ fun n _ => ?_
      obtain ⟨l, hl⟩ := hp3 n _ (MvPolynomial.homogeneousComponent_isHomogeneous n f)
      rw [hl]
      refine Submodule.sum_mem _ fun b _ => ?_
      exact Submodule.mem_iSup_of_mem (⟨n, b⟩ : Σ n : ℕ, (Fin n → ι)) ⟨l b, rfl⟩
  let S : Subrepresentation (ltrRep ρ) :=
    ⟨U, fun g v hv => hU _ (hρ ▸ ⟨g⁻¹, rfl⟩) v hv⟩
  obtain ⟨S', hS'⟩ := hsemi.exists_isCompl S
  refine ⟨S'.toSubmodule, ?_, ?_⟩
  · rintro g hg f hf
    rw [← hρ] at hg
    obtain ⟨g, rfl⟩ := hg
    have := S'.apply_mem_toSubmodule g⁻¹ hf
    change ltr (ρ g⁻¹⁻¹) f ∈ _ at this
    rwa [inv_inv] at this
  · constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hS'.1)
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hS'.2)

end GlobalTheory.ClassFin
