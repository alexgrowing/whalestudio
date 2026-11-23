import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier
open scoped TensorProduct

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem exists_openImmersion_ringOn (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) : ∃ ι : Sp (M.ringOn U) ⟶ M.Z, IsOpenImmersion ι ∧ Set.range ι = U ∧
      ι ≫ M.s = spMap (algebraMap F (M.ringOn U)) := by
  let e : Γ(M.Z, U) ≅ CommRingCat.of (M.ringOn U) := (M.sectionsEquiv U hne).toCommRingCatIso
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU e.hom
  have hv : ∀ f, valR (Spec.map e.hom ≫ hU.fromSpec) U f = M.sectionsEquiv U hne f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map e.hom ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (Spec.map e.hom).surjective.range_eq,
      Set.image_univ, hU.range_fromSpec]
  · rw [← Spec.map_preimage ((Spec.map e.hom ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← GlobalTheory.Points.valR_constFn M.s _ U hx, hv]
    exact Subtype.ext ((RatModel.coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b))

theorem exists_openImmersion_tensor (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) {K : Type} [Field K] [Algebra F K] {Z : Scheme.{0}} {p : Z ⟶ M.Z} {q : Z ⟶ Sp K}
    (h : IsPullback p q M.s (spMap (algebraMap F K))) :
    ∃ j : Sp (M.ringOn U ⊗[F] K) ⟶ Z, IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
  obtain ⟨ι, hι, hr, hs⟩ := exists_openImmersion_ringOn M hU hne
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct F (M.ringOn U) K)
  rw [show Spec.map (CommRingCat.ofHom (algebraMap F (M.ringOn U))) = ι ≫ M.s from hs.symm] at h1
  let j := h.lift (_ ≫ ι) _ ((Category.assoc _ _ _).trans h1.w)
  have h2 : IsPullback j _ p ι :=
    (IsPullback.of_bot (h₁₁ := _) (by simpa [j] using h1) (h.lift_fst _ _ _).symm h).flip
  refine ⟨j, MorphismProperty.of_isPullback h2.flip hι, ?_⟩
  refine Eq.trans ?_ (congrArg (p ⁻¹' ·) hr)
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, ← h2.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback h2 z w hw.symm
    exact ⟨v, hv⟩

theorem nonempty_algEquiv_adjoin (φ : Ω →ₐ[F] Ω') (A : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) :
    Nonempty (MvPolynomial σ A ≃ₐ[F] Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t)) := by
  let ψ : MvPolynomial σ A →ₐ[F] Ω' := MvPolynomial.aevalTower (φ.comp A.val) t
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    refine MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective ?_
    rw [map_zero]
    refine ht _ ?_
    rw [MvPolynomial.eval₂_map]
    exact hP
  have hr : ψ.range = Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨P, rfl⟩
      show ψ P ∈ _
      induction P using MvPolynomial.induction_on with
      | C a => exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, by simp [ψ]⟩)
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul]
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, by simp [ψ]⟩))
    · rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [ψ]⟩
      · exact ⟨MvPolynomial.X i, by simp [ψ]⟩
  exact ⟨(AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hr)⟩

theorem isDomain_mvPolynomial_tensor (A K σ : Type) [CommRing A] [Algebra F A] [CommRing K] [Algebra F K]
    [IsDomain (A ⊗[F] K)] : IsDomain (MvPolynomial σ A ⊗[F] K) := by
  let e1 : MvPolynomial σ A ⊗[F] K ≃ₐ[F] (A ⊗[F] MvPolynomial σ F) ⊗[F] K :=
    Algebra.TensorProduct.congr ((MvPolynomial.algebraTensorAlgEquiv F A).symm.restrictScalars F) AlgEquiv.refl
  let e2 : (A ⊗[F] MvPolynomial σ F) ⊗[F] K ≃ₐ[F] (A ⊗[F] K) ⊗[F] MvPolynomial σ F :=
    (Algebra.TensorProduct.assoc F F F A (MvPolynomial σ F) K).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm F _ _)).trans
        (Algebra.TensorProduct.assoc F F F A K (MvPolynomial σ F)).symm)
  let e3 := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F (A ⊗[F] K)
  exact (((e1.trans e2).toRingEquiv).trans e3.toRingEquiv).toMulEquiv.isDomain _

theorem AffCover.geometricallyIntegral : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r →
    GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  intro F Ω Ω' _ _ _ _ _ M M' φ f r h hM
  refine ⟨geometrically_iff_of_commRing.2 fun K _ _ Z p q hZ => ?_⟩
  have hI : IsIntegral (pullback M.s (spMap (algebraMap F K))) :=
    pullback_of_geometrically hM.geometrically_isIntegral K _
  have key : ∀ z' : M'.Z, ∃ (U : M'.Z.Opens) (Y : Scheme.{0}) (j : Y ⟶ Z), z' ∈ U ∧ IsIntegral Y ∧
      IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
    intro z'
    obtain ⟨U, W, t, hU, hW, hz, hUW, ht, hR⟩ := h.2 z'
    have hWne : (W : Set M.Z).Nonempty := ⟨_, hUW z' hz⟩
    obtain ⟨i, hi, -⟩ := exists_openImmersion_tensor M hW hWne (IsPullback.of_hasPullback M.s (spMap (algebraMap F K)))
    have : Nontrivial (M.ringOn W ⊗[F] K) := inferInstance
    have : IsIntegral (Sp (M.ringOn W ⊗[F] K)) := isIntegral_of_isOpenImmersion i
    have : IsDomain (M.ringOn W ⊗[F] K) := (affine_isIntegral_iff (CommRingCat.of _)).1 this
    have := isDomain_mvPolynomial_tensor (F := F) (M.ringOn W) K (Fin r)
    obtain ⟨e⟩ := nonempty_algEquiv_adjoin φ (M.ringOn W) t ht
    rw [← hR] at e
    have : IsDomain (M'.ringOn U ⊗[F] K) :=
      (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (A₁ := K) (R := F))).toMulEquiv.isDomain _
    obtain ⟨j, hj, hr⟩ := exists_openImmersion_tensor M' hU ⟨_, hz⟩ hZ
    exact ⟨U, _, j, hz, inferInstance, hj, hr⟩
  have hred : IsReduced Z := by
    have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
      obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (p z)
      obtain ⟨y, rfl⟩ : z ∈ Set.range j := hr ▸ hz
      exact isReduced_of_injective (j.stalkMap y).hom (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk Z
  have hopen : UniversallyOpen p := MorphismProperty.of_isPullback hZ.flip inferInstance
  have hirr : IrreducibleSpace Z := by
    obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (genericPoint M'.Z)
    have h1 : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _ j.continuous.continuousOn
    have h2 : Dense (Set.range j) := by
      rw [hr]
      exact (U.isOpen.dense ⟨_, hz⟩).preimage p.isOpenMap
    have h3 := h1.closure
    rw [h2.closure_eq] at h3
    exact (irreducibleSpace_def Z).2 h3
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end GlobalTheory.FlagBundle
