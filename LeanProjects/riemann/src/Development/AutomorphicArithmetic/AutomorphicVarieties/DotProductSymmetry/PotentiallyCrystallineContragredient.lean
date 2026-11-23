import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedIsCrysDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFilStatement
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

private def tinv {Γ R : Type} [Group Γ] [CommRing R] {n : ℕ} (r : Γ →* GL (Fin n) R) : Γ →* GL (Fin n) R where
  toFun s := ⟨((r s)⁻¹).val.transpose, (r s).val.transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' s t := by
    apply Units.ext
    simp [Matrix.transpose_mul]

private theorem tinv_val {Γ R : Type} [Group Γ] [CommRing R] {n : ℕ} (r : Γ →* GL (Fin n) R) (s : Γ) :
    (tinv r s).val = (r s⁻¹).val.transpose := by
  rw [map_inv]
  rfl

private theorem dot_symm {L Γ : Type} [Field L] [Group Γ] {n : ℕ} (ρ ρ' : Representation L Γ (Fin n → L))
    (h : ∀ g x y, x ⬝ᵥ ρ g⁻¹ y = ρ' g x ⬝ᵥ y) (g : Γ) (φ : Module.Dual L (Fin n → L)) :
    (dotProductEquiv L (Fin n)).symm (ρ.dual g φ) = ρ' g ((dotProductEquiv L (Fin n)).symm φ) := by
  obtain ⟨x, rfl⟩ := (dotProductEquiv L (Fin n)).surjective φ
  apply (dotProductEquiv L (Fin n)).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  refine LinearMap.ext fun y => ?_
  exact h g x y

theorem UpperTheory.potentiallyCrystalline_contragredient :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
        (r r' : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω),
        (∀ s, (r' s).val = ((r s)⁻¹).val.transpose) → UpperTheory.V.Af.PotCrysAt r A → UpperTheory.V.Af.PotCrysAt r' A := by
  intro F Ω _ _ _ _ _ l _ n r r' A h hp
  obtain ⟨O, i1, i2, i3, Bw, hj, L₁, r₁, hm, K', hK, hc⟩ := hp
  refine ⟨O, i1, i2, i3, Bw, hj, L₁, tinv r₁, ⟨hm.1, ?_⟩, K', hK, ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    have e1 : r (g : G F Ω)⁻¹ = Formalism.MainNotions.N.mapRep (algebraMap ↥L₁.1 (Formalism.BasicNotions.Loc.Om l)) r₁ g⁻¹ :=
      (DFunLike.congr_fun hm.2 g⁻¹).symm
    have e2 : ((r' (g : G F Ω)) : Matrix (Fin n) (Fin n) (Qbar l)) = (r (g : G F Ω)⁻¹).val.transpose := by
      rw [h, map_inv]
    change (algebraMap ↥L₁.1 (Formalism.BasicNotions.Loc.Om l)).mapMatrix (tinv r₁ g).val = (r' (g : G F Ω)).val
    rw [e2, e1, tinv_val]
    rfl
  · obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
    have := L₁.2
    have hd := GlobalTheory.Per.TiedDual.tied_isCrys_dual l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) T
      (GlobalTheory.T.periodRings_regular_phi_surjective_fil l _ _ T).1 K' L₁ _ _ hc
    refine Formalism.MainNotions.N.K.Norm.isCrys_congr _ (dotProductEquiv ↥L₁.1 (Fin n)).symm
      (dot_symm _ _ fun g x y => ?_) hd
    change x ⬝ᵥ (Bw.repE L₁ r₁ _ y) = (Bw.repE L₁ (tinv r₁) _ x) ⬝ᵥ y
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, tinv_val, Matrix.mulVec_transpose,
      Matrix.dotProduct_mulVec, map_inv, map_inv, map_inv]
