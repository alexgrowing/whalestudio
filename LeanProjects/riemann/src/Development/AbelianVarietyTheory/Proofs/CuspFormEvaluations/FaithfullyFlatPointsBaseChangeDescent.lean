import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct in
theorem faithfullyFlat_of_geometric_points (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B)
    (hφ : φ.Flat)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K), ∃ χ : B →+* K, χ.comp φ = ψ) :
    φ.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨hφ, fun p => ?_⟩
  obtain ⟨χ, hχ⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    ((algebraMap p.asIdeal.ResidueField _).comp (algebraMap S p.asIdeal.ResidueField))
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, ?_⟩
  ext x
  have hx := RingHom.congr_fun hχ x
  simp only [RingHom.comp_apply] at hx
  change χ (φ x) = 0 ↔ _
  rw [hx, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]

theorem flat_comp_localizationAway (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B) (e : B)
    (hφ : φ.Flat) : ((algebraMap B (Localization.Away e)).comp φ).Flat :=
  hφ.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers e)))

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_faithfullyFlat_pushout (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁]
    [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁)
    (φ₂ : S →ₐ[F] S₂) (h : φ₂.toRingHom.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁ := by
  letI : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  letI : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S₂ := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra F (S₁ ⊗[S] S₂) :=
    ((Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂).comp
      (algebraMap F S₁)).toAlgebra
  have hff : (algebraMap S₁ (S₁ ⊗[S] S₂)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine ⟨S₁ ⊗[S] S₂, inferInstance, inferInstance,
    { (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂) with commutes' := fun c => rfl },
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom with
      commutes' := fun c => ?_ }, ?_, hff, hff.injective⟩
  · show (1 : S₁) ⊗ₜ[S] algebraMap F S₂ c = algebraMap F S₁ c ⊗ₜ[S] (1 : S₂)
    rw [← φ₁.commutes, ← φ₂.commutes]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm
  · exact AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat (F S S' : Type) [Field F] [CommRing S]
    [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S')
    (h : φ.toRingHom.FaithfullyFlat) (w : S')
    (hw : ∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T),
      ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) : ∃! v : S, φ v = w := by
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := RingHom.faithfullyFlat_algebraMap_iff.1 h
  have hinj := h.injective
  letI : Algebra F (S' ⊗[S] S') :=
    ((Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S').comp
      (algebraMap F S')).toAlgebra
  let ψ₁ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S') with commutes' := fun c => rfl }
  let ψ₂ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom with
      commutes' := fun c => by
        show (1 : S') ⊗ₜ[S] algebraMap F S' c = algebraMap F S' c ⊗ₜ[S] (1 : S')
        rw [← φ.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm }
  have hcomp : ψ₁.comp φ = ψ₂.comp φ :=
    AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s
  have hw' : w ⊗ₜ[S] (1 : S') = (1 : S') ⊗ₜ[S] w := hw (S' ⊗[S] S') ψ₁ ψ₂ hcomp
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' w).1
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact hw')
  exact ⟨v, hv, fun v' hv' => hinj (hv'.trans hv.symm)⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.faithfullyFlat_points_baseChange_descent : (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), φ.Flat → (∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K), ∃ χ : B →+* K, χ.comp φ = ψ) → φ.FaithfullyFlat) ∧ (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B) (e : B), φ.Flat → ((algebraMap B (Localization.Away e)).comp φ).Flat) ∧ (∀ (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁] [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁) (φ₂ : S →ₐ[F] S₂), φ₂.toRingHom.FaithfullyFlat → ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T), ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁) ∧ ∀ (F S S' : Type) [Field F] [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S'), φ.toRingHom.FaithfullyFlat → ∀ w : S', (∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T), ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) → ∃! v : S, φ v = w := by
  refine ⟨fun S B _ _ φ hflat hpt => ?_, fun S B _ _ φ e hflat => ?_,
    fun F S S₁ S₂ _ _ _ _ _ _ _ φ₁ φ₂ h => _root_.GlobalTheory.exists_faithfullyFlat_pushout F S S₁ S₂ φ₁ φ₂ h,
    fun F S S' _ _ _ _ _ φ h w hw => _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat F S S' φ h w hw⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨hflat, fun p => ?_⟩
    obtain ⟨χ, hχ⟩ := hpt (AlgebraicClosure p.asIdeal.ResidueField)
      ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
        (algebraMap S p.asIdeal.ResidueField))
    refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext ?_⟩
    show Ideal.comap φ (RingHom.ker χ) = p.asIdeal
    rw [RingHom.comap_ker, hχ, RingHom.ker_comp_of_injective _
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).injective,
      Ideal.ker_algebraMap_residueField]
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.2 inferInstance)

end GlobalTheory
