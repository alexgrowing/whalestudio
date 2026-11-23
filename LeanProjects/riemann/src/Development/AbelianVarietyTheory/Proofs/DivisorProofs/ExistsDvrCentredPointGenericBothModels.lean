import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrCentre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFunctionFieldOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrTrait
open GlobalTheory.Points

theorem exists_factor_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) (hy : ∀ w, y w = genericPoint M.Z) :
    ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  refine ⟨β, ?_⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 := top_le_preimage_of_specializes hs hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
  exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

theorem exists_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y X M : RatModel o Ω)
    (f : M.Z ⟶ X.Z) (d : Y.Z ⟶ X.Z), X.IsHom M (AlgHom.id o Ω) f → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d →
    ∀ z : M.Z, f z ∈ Set.range d → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z) (κ : Ω →+* FractionRing V), z ∈ Set.range ξ ∧
      spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt ∧
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt := by
  intro o Ω _ _ _ _ Y X M f d hf hd hop z hz
  obtain ⟨V, _, _, _, _, ξ, -, hξ, w, hw⟩ := GlobalTheory.DvrCentre.exists_complete_dvr_centre o Ω M z
  have ef : M.pt ≫ f = X.pt := by
    have h := hf
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have ed : Y.pt ≫ d = X.pt := by
    have h := hd
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have hbot : ξ (⊥ : PrimeSpectrum V) = genericPoint M.Z := by
    have h2 : (⊥ : PrimeSpectrum V) ⤳ w := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have h3 := h2.map ξ.continuous
    rw [hw] at h3
    exact (h3.antisymm (genericPoint_specializes _)).eq
  have hy : ∀ u, (spMap (algebraMap V (FractionRing V)) ≫ ξ) u = genericPoint M.Z := fun u => by
    refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg ξ ?_) hbot)
    rw [Subsingleton.elim u (⊥ : PrimeSpectrum (FractionRing V))]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V)))
  obtain ⟨κ, hκ⟩ := exists_factor_pt M _ hy
  have hsp : ∀ u : Sp V, (ξ ≫ f) u ⤳ f z := fun u => by
    rw [← hξ, Scheme.Hom.comp_apply]
    exact ((IsLocalRing.specializes_closedPoint (R := V) u).map ξ.continuous).map f.continuous
  have hr : Set.range (ξ ≫ f) ⊆ Set.range d := by
    rintro _ ⟨u, rfl⟩
    exact (hsp u).mem_open d.isOpenEmbedding.isOpen_range hz
  refine ⟨V, inferInstance, inferInstance, inferInstance, ξ, IsOpenImmersion.lift d (ξ ≫ f) hr, κ,
    ⟨_, hξ⟩, hκ, ?_⟩
  rw [← cancel_mono d, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hκ, Category.assoc,
    Category.assoc, ef, ed]

end GlobalTheory.DvrTrait
