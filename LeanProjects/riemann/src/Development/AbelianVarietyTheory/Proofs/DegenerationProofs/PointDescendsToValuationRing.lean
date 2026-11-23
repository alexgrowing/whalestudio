import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_range_of_dominating {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {W C : Type} [CommRing W]
    [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C) (hα : IsLocalHom α)
    (hβ : Function.Injective β) (hc : β.comp α = ga.comp (algebraMap V (FractionRing V)))
    (a : FractionRing V) (w : W) (h : β w = ga a) : a ∈ (algebraMap V (FractionRing V)).range := by
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, hv⟩
  · by_cases ha : a = 0
    · exact ha ▸ Subring.zero_mem _
    have h1 : β (α v) = ga a⁻¹ := by rw [← hv]; exact congrArg (· v) (congrArg DFunLike.coe hc)
    have h2 : α v * w = 1 := hβ (by rw [map_mul, h1, h, ← map_mul, inv_mul_cancel₀ ha, map_one, map_one])
    obtain ⟨u, rfl⟩ := hα.map_nonunit v (IsUnit.of_mul_eq_one _ h2)
    refine ⟨(u⁻¹ : Vˣ), ?_⟩
    rw [← inv_inv a, ← hv]
    exact map_units_inv _ u

theorem point_descends_to_valuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  intro V _ _ _ W C _ _ _ α β ga hα hβ hc X y x hxy
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (IsLocalRing.closedPoint W)) trivial
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of W) y hp).ge
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    intro p _
    have h1 : (spMap β ≫ y) (IsLocalRing.closedPoint C) ∈ U := hy (x := spMap β _) trivial
    rw [hxy] at h1
    obtain rfl : p = spMap ga (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) _ _
    exact h1
  have key : ∀ f, β (valR y U f) = ga (valR x U f) := fun f => by
    rw [← HolHom.valR_spMap β y U hy, ← HolHom.valR_spMap ga x U hx, hxy]
  have hinj := IsFractionRing.injective V (FractionRing V)
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((HolHom.evalHom x U hx).codRestrict _ fun f =>
    mem_range_of_dominating α β ga hα hβ hc _ _ ((key f).trans (by rw [HolHom.valR_eq _ _ hx])))
  have hφ : ∀ f, algebraMap V (FractionRing V) (φ f) = valR x U f := fun f => by
    rw [HolHom.valR_eq _ _ hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let h : Sp V ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hh : ⊤ ≤ h ⁻¹ᵁ U := fun p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR h U f = φ f := fun f => by
    rw [HolHom.valR_eq _ _ hh]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom φ) hh)
  refine ⟨h, HolHom.point_ext hU (fun p _ => hh (x := spMap α p) trivial) hy fun f => ?_,
    HolHom.point_ext hU (fun p _ => hh (x := jK V p) trivial) hx fun f => ?_⟩
  · rw [HolHom.valR_spMap _ _ _ hh, hval]
    refine hβ ?_
    rw [key, ← hφ]
    exact congrArg (· (φ f)) (congrArg DFunLike.coe hc)
  · exact (HolHom.valR_spMap (algebraMap V (FractionRing V)) _ _ hh f).trans (by rw [hval, hφ])

end GlobalTheory
