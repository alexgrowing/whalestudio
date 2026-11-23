import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.NonlocalTrait

theorem exists_common_ext {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F L₁ L₂)
  letI := Ideal.Quotient.field m
  refine ⟨TensorProduct F L₁ L₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem torusExtension_iterate {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G))) :
    Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G))) := by
  obtain ⟨T⟩ := h
  exact ⟨torusExtOfIso (pullCompIso b a G) T⟩

theorem torusExtension_compose {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  exact ⟨torusExtOfIso (pullCompIso b a G).symm T⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.NonlocalTrait

open GlobalTheory.NonlocalTrait in

theorem GlobalTheory.exists_trait_nonlocal_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  intro R _ _ _ _ G _ hG W _ _ g hg
  set p : Ideal R := Ideal.comap g (maximalIdeal W) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  obtain ⟨r₀, hr₀u, hr₀⟩ : ∃ r, IsUnit (g r) ∧ ¬ IsUnit r := by
    by_contra h
    push_neg at h
    exact hg ⟨fun r hr => h r hr⟩
  have hr₀p : r₀ ∉ p := fun h => ((mem_maximalIdeal _).1 (Ideal.mem_comap.1 h)) hr₀u
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  haveI : IsLocalRing (R ⧸ p) := .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hunit : ∀ r : R, IsUnit (Ideal.Quotient.mk p r) → IsUnit r := by
    intro r hr
    obtain ⟨b, hb⟩ := hr.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra hru
    have h1 : r * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hru
    have h2 : r * y - 1 ∈ maximalIdeal R :=
      hpm (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_sub, map_mul, hb, map_one, sub_self]))
    have h3 := (maximalIdeal R).sub_mem h1 h2
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hA : ¬ IsField (R ⧸ p) := by
    intro hF
    have h0 : Ideal.Quotient.mk p r₀ ≠ 0 := fun h => hr₀p (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
    exact hr₀ (hunit r₀ (Units.mkOfMulEqOne _ b hb).isUnit)
  let k₀ := FractionRing (R ⧸ p)
  let φ₀ : R →+* k₀ := (algebraMap (R ⧸ p) k₀).comp (Ideal.Quotient.mk p)
  let σ : k₀ →+* AlgebraicClosure k₀ := algebraMap k₀ (AlgebraicClosure k₀)
  let G₀ := (Over.pullback (spMap φ₀)).obj G
  have hG₀ : IsSemiAbelian G₀ := IsSemiAbelian.pullback _ G hG
  haveI := hG₀.smooth
  haveI := hG₀.quasiCompact
  haveI := hG₀.separated
  have T₀ : Nonempty (TorusExtension ((Over.pullback (spMap σ)).obj G₀)) :=
    torusExtension_iterate _ _ G (by rw [← spMap_comp']; exact hG.fibres _ _)
  obtain ⟨T⟩ := T₀
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ G₀ T
  haveI : Finite s := hs.to_subtype
  let k' := IntermediateField.adjoin k₀ s
  haveI : FiniteDimensional k₀ k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  letI : Algebra (R ⧸ p) k' := ((algebraMap k₀ k').comp (algebraMap (R ⧸ p) k₀)).toAlgebra
  haveI : IsScalarTower (R ⧸ p) k₀ k' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨V, hV, hdom⟩ := (discreteValuationRing_dominating_noetherian_local (R := R ⧸ p) (K := k₀) k').1 hA
  rw [LocalSubring.le_def] at hdom
  obtain ⟨hsub, hloc⟩ := hdom
  have hmem : ∀ a : R ⧸ p, algebraMap (R ⧸ p) k' a ∈ V := fun a => hsub ⟨a, rfl⟩
  have hinjA : Function.Injective (algebraMap (R ⧸ p) k') :=
    (algebraMap k₀ k').injective.comp (IsFractionRing.injective (R ⧸ p) k₀)
  let ψA : (R ⧸ p) →+* V := (algebraMap (R ⧸ p) k').codRestrict V hmem
  let ψ : R →+* V := ψA.comp (Ideal.Quotient.mk p)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun r hr => hunit r ?_⟩
    set a := Ideal.Quotient.mk p r
    have h1 : IsUnit (Subring.inclusion hsub ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩) := hr
    obtain ⟨⟨u, v, huv, _⟩, hu⟩ := hloc.map_nonunit _ h1
    have hu' : u = ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩ := hu
    subst hu'
    obtain ⟨b, hb⟩ := v.2
    refine (Units.mkOfMulEqOne a b (hinjA ?_)).isUnit
    have := congrArg Subtype.val huv
    rw [map_mul, map_one, hb]
    exact this
  let κ := ResidueField W
  let gA : (R ⧸ p) →+* κ := Ideal.Quotient.lift p ((residue W).comp g) (fun a ha => by
    show residue W (g a) = 0
    exact (residue_eq_zero_iff _).2 (Ideal.mem_comap.1 ha))
  have hgA : Function.Injective gA := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : residue W (g r) = 0 := ha
    have : g r ∈ maximalIdeal W := (residue_eq_zero_iff _).1 ha'
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 this)
  let g₀ : k₀ →+* κ := IsFractionRing.lift hgA
  let e : k' ≃ₐ[V] FractionRing V := IsLocalization.algEquiv (nonZeroDivisors V) k' (FractionRing V)
  let α₀ : k₀ →+* FractionRing V := e.toRingEquiv.toRingHom.comp (algebraMap k₀ k')
  let β₀ : FractionRing V →+* AlgebraicClosure k₀ := (algebraMap k' (AlgebraicClosure k₀)).comp e.symm.toRingEquiv.toRingHom
  have hβα : β₀.comp α₀ = σ := by
    ext x
    simp [α₀, β₀, σ]
  have hsr : s ⊆ Set.range β₀ := fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin k₀ s hx⟩, by simp [β₀]⟩
  have T₂ := torusExtension_compose _ _ G (H (FractionRing V) α₀ β₀ hβα hsr)
  have key : α₀.comp φ₀ = (algebraMap V (FractionRing V)).comp ψ := by
    ext r
    show e (algebraMap k₀ k' (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) =
      algebraMap V (FractionRing V) (ψA (Ideal.Quotient.mk p r))
    rw [← e.commutes]
    rfl
  obtain ⟨L, _, i, j, hij⟩ := exists_common_ext α₀ g₀
  refine ⟨V, inferInstance, inferInstance, hV, ψ, L, inferInstance, i, j.comp (residue W), hψ, ?_, ?_, ?_⟩
  · intro x hx
    simp [(residue_eq_zero_iff x).2 hx]
  · rw [RingHom.comp_assoc, ← key]
    ext r
    have h1 := congrArg (fun f => f (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) hij
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    show i (α₀ (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) = _
    rw [h1]
    simp [g₀, gA, φ₀, IsFractionRing.lift_algebraMap]
  · rw [← key, spMap_comp']
    exact T₂
