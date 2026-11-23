import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmooth1Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.StalkOfAlgebra

theorem stalk_of_smoothAt {R A : CommRingCat.{0}} (φ : R ⟶ A) (p : PrimeSpectrum A)
    (h : letI := φ.hom.toAlgebra; Algebra.IsSmoothAt R p.asIdeal) :
    ((Spec.map φ).stalkMap p).hom.FormallySmooth := by
  letI := φ.hom.toAlgebra
  let P := (p.comap φ.hom).asIdeal
  haveI : p.asIdeal.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P p.asIdeal
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  have : Algebra.FormallySmooth (Localization.AtPrime P) (Localization.AtPrime p.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Localization.AtPrime P)).mp h
  exact this

theorem core (hA : LateralTheory.E.SpreadingOutSmoothness.LeafAlgDescend) (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (R : Subalgebra k Ω) {C : Scheme.{0}} {A : CommRingCat.{0}} (φ : CommRingCat.of R ⟶ A)
    (c : C ⟶ Sp Ω) (v : C ⟶ Spec A) [LocallyOfFinitePresentation (Spec.map φ)] (hs : Smooth c)
    (hv : IsPullback v c (Spec.map φ) (toR R)) (y : C) : v y ∈ (Spec.map φ).smoothLocus := by
  letI : Algebra R A := φ.hom.toAlgebra
  have hfp0 : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp inferInstance
  have hfp : Algebra.FinitePresentation R A := hfp0
  have hpo := (CommRingCat.isPushout_tensorProduct R Ω A)
  have hφ : CommRingCat.ofHom (algebraMap R A) = φ := rfl
  rw [hφ] at hpo
  have hstd := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  let e := hv.isoIsPullback _ _ hstd
  have h1 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom) = v :=
    hv.isoIsPullback_hom_fst _ _ hstd
  have h2 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = c :=
    hv.isoIsPullback_hom_snd _ _ hstd
  haveI := hs
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = e.inv ≫ c := by
      rw [← h2, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hrs := (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)).mp hsm
  have hinc : (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] A) = algebraMap Ω (Ω ⊗[R] A) := by
    ext x; rfl
  have hsA : Algebra.Smooth Ω (Ω ⊗[R] A) := by
    rw [← RingHom.smooth_algebraMap, ← hinc]; exact hrs
  have key := hA k Ω R A hfp hsA (e.hom y)
  rw [← h1, Scheme.Hom.comp_apply]
  exact stalk_of_smoothAt φ _ key

theorem LeafStalkOfAlg_of : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := by
  intro hA k _ Ω _ _ R _ C D c q v hD _ hs hv y
  let e := D.isoSpec
  let φ := Spec.preimage (e.inv ≫ q)
  have hq : Spec.map φ = e.inv ≫ q := Spec.map_preimage _
  haveI : LocallyOfFinitePresentation (Spec.map φ) := by rw [hq]; infer_instance
  have hv' : IsPullback (v ≫ e.hom) c (Spec.map φ) (toR R) := by
    rw [hq]
    exact hv.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have key := core hA k Ω R φ c (v ≫ e.hom) hs.smooth hv' y
  have h2 := Scheme.Hom.preimage_smoothLocus_eq e.hom (Spec.map φ)
  have h3 : e.hom ≫ Spec.map φ = q := by rw [hq, Iso.hom_inv_id_assoc]
  have h4 : v y ∈ (e.hom ≫ Spec.map φ).smoothLocus := by
    rw [← h2]; simpa [Scheme.Hom.comp_apply] using key
  rw [Scheme.Hom.mem_smoothLocus] at h4 ⊢
  rwa [h3] at h4

end LateralTheory.E.StalkOfAlgebra

end
