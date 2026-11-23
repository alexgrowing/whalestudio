import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.GaloisPoints

theorem exists_factor_of_fixed {K L : Type} [Field K] [CharZero K] [Field L] [Algebra K L]
    (em : L →ₐ[K] AlgebraicClosure K) {Y : Scheme} (y : Sp (AlgebraicClosure K) ⟶ Y)
    (h : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ a, σ (em a) = em a) →
      spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp L ⟶ Y, spMap em.toRingHom ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField (AlgebraicClosure K) Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField (AlgebraicClosure K) Y).symm ⟨p, φ⟩ =
      Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ em.fieldRange := by
    intro b
    rw [← InfiniteGalois.fixedField_fixingSubgroup em.fieldRange, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ (fun a => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩)
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  let e : L ≃ₐ[K] em.fieldRange := AlgEquiv.ofInjectiveField em
  let ψ : Y.residueField p →+* L :=
    e.symm.toAlgHom.toRingHom.comp (φ.hom.codRestrict em.fieldRange hmem)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext b
  have : ∀ c, em c = (e c : AlgebraicClosure K) := fun c => rfl
  show em (e.symm ⟨φ.hom b, hmem b⟩) = φ.hom b
  rw [this, e.apply_symm_apply]

theorem exists_sigma_iso {K : Type} [Field K] (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] :
    ∃ (I : Type) (L : I → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
      (e : (∐ fun i => Sp (L i)) ≅ X.left), (∀ i, Algebra.IsAlgebraic K (L i)) ∧
      ∀ i, Sigma.ι (fun i => Sp (L i)) i ≫ e.hom ≫ X.hom = spMap (algebraMap K (L i)) := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let A : CommRingCat := Γ(X.left, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hφ : Spec.map φ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  have hE : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hE' : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hE
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Algebra.Etale K A := hE'
  obtain ⟨I, hI, L, iF, iA, e, hs⟩ := (Algebra.FormallyEtale.iff_exists_algEquiv_prod K A).1 inferInstance
  let e' : A ≅ CommRingCat.of (∀ i, L i) := e.toRingEquiv.toCommRingCatIso
  refine ⟨I, L, iF, iA, asIso (sigmaSpec fun i => CommRingCat.of (L i)) ≪≫
    asIso (Spec.map e'.hom) ≪≫ X.left.isoSpec.symm, fun i => inferInstance, fun i => ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc]
  rw [← hφ, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact congrFun (e.commutes a) i

theorem exists_hom_of_equivariant : ∀ (K : Type) [Field K] [CharZero K] (X Y : Over (Sp K)), IsFinite X.hom → Etale X.hom → ∀ f : (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X) → (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ Y), (∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x x', x'.left = spMap σ.toAlgHom.toRingHom ≫ x.left → (f x').left = spMap σ.toAlgHom.toRingHom ≫ (f x).left) → ∃ u : X ⟶ Y, ∀ x, x ≫ u = f x := by
  intro K _ _ X Y _ _ f hf
  obtain ⟨I, L, iF, iA, e, halg, he⟩ := exists_sigma_iso X
  let em : ∀ i, L i →ₐ[K] AlgebraicClosure K := fun i => IsAlgClosed.lift
  have hem : ∀ i (j : L i →ₐ[K] AlgebraicClosure K),
      spMap j.toRingHom ≫ spMap (algebraMap K (L i)) = spMap (algebraMap K (AlgebraicClosure K)) := by
    intro i j
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact j.commutes a
  let x₀ : ∀ i, (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X) := fun i =>
    Over.homMk (spMap (em i).toRingHom ≫ Sigma.ι (fun i => Sp (L i)) i ≫ e.hom) (by
      simp only [Category.assoc, he]
      exact hem i _)
  have hx₀ : ∀ i, (x₀ i).left = spMap (em i).toRingHom ≫ Sigma.ι (fun i => Sp (L i)) i ≫ e.hom :=
    fun i => rfl
  have hz : ∀ i, ∃ z : Sp (L i) ⟶ Y.left, spMap (em i).toRingHom ≫ z = (f (x₀ i)).left := by
    intro i
    refine exists_factor_of_fixed (em i) _ fun σ hσ => (hf σ (x₀ i) (x₀ i) ?_).symm
    rw [hx₀]
    erw [← Category.assoc (spMap σ.toAlgHom.toRingHom), ← Spec.map_comp]
    congr 2
    ext a
    exact (hσ a).symm
  choose z hz using hz
  have hzw : ∀ i, z i ≫ Y.hom = spMap (algebraMap K (L i)) := by
    intro i
    have h1 : spMap (em i).toRingHom ≫ z i ≫ Y.hom =
        spMap (em i).toRingHom ≫ spMap (algebraMap K (L i)) := by
      rw [← Category.assoc, hz, hem]
      exact Over.w (f (x₀ i))
    rw [← Spec.map_preimage (z i ≫ Y.hom)] at h1 ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h1
    congr 1
    ext a
    exact (em i).toRingHom.injective (congrArg (fun ψ => ψ.hom a) h1)
  refine ⟨Over.homMk (e.inv ≫ Sigma.desc z) ?_, fun x => ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc_assoc]
    exact (hzw i).trans (he i).symm
  · let w : Sp (AlgebraicClosure K) ⟶ ∐ fun i => Sp (L i) := x.left ≫ e.inv
    obtain ⟨i, q, hq⟩ : ∃ (i : I) (q : Sp (L i)),
        Sigma.ι (fun i => Sp (L i)) i q = w (closedPoint (AlgebraicClosure K)) :=
      (sigmaOpenCover fun i => Sp (L i)).exists_eq _
    have hr : Set.range w ⊆ Set.range (Sigma.ι (fun i => Sp (L i)) i) := by
      rintro _ ⟨t, rfl⟩
      obtain rfl : t = closedPoint (AlgebraicClosure K) := Subsingleton.elim _ _
      exact ⟨q, hq⟩
    let v : Sp (AlgebraicClosure K) ⟶ Sp (L i) := IsOpenImmersion.lift _ w hr
    have hv : v ≫ Sigma.ι (fun i => Sp (L i)) i = w := IsOpenImmersion.lift_fac _ _ _
    have hv2 : v ≫ spMap (algebraMap K (L i)) = spMap (algebraMap K (AlgebraicClosure K)) := by
      rw [← he, ← Category.assoc, hv]
      simp only [w, Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨v', hv'⟩ := Spec.map_surjective v
    rw [← hv', ← Spec.map_comp, Spec.map_inj] at hv2
    let j : L i →ₐ[K] AlgebraicClosure K :=
      { v'.hom with commutes' := fun a => congrArg (fun ψ => ψ.hom a) hv2 }
    obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ a, σ (em i a) = j a := by
      letI : Algebra (L i) (AlgebraicClosure K) := (em i).toRingHom.toAlgebra
      haveI : IsScalarTower K (L i) (AlgebraicClosure K) :=
        IsScalarTower.of_algebraMap_eq fun a => ((em i).commutes a).symm
      refine ⟨AlgEquiv.ofBijective (j.liftNormal (AlgebraicClosure K)) (AlgHom.normal_bijective K _ _ _), fun a => ?_⟩
      exact j.liftNormal_commutes (AlgebraicClosure K) a
    have hvσ : v = spMap σ.toAlgHom.toRingHom ≫ spMap (em i).toRingHom := by
      rw [← hv', ← Spec.map_comp]
      congr 1
      ext a
      exact (hσ a).symm
    have hx : x.left = spMap σ.toAlgHom.toRingHom ≫ (x₀ i).left := by
      rw [hx₀]
      erw [← Category.assoc, ← hvσ, ← Category.assoc, hv]
      simp [w]
    ext1
    rw [hf σ _ _ hx, ← hz]
    have h1 : w ≫ Sigma.desc z =
        spMap σ.toAlgHom.toRingHom ≫ spMap (em i).toRingHom ≫ z i := by
      rw [← hv, Category.assoc, Sigma.ι_desc, hvσ, Category.assoc]
    exact (Category.assoc _ _ _).symm.trans h1

end GlobalTheory.GaloisPoints
