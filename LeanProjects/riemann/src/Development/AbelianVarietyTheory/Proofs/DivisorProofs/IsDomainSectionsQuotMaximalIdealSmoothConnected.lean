import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem abLawCst_eq_smallExtLiftCst {X : Scheme} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    GlobalTheory.AbLaw.cst f U = GlobalTheory.SmallExtLift.cst f U := by
  ext r
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.SmallExtLift.cst, GlobalTheory.AbLaw.rs, Scheme.Hom.appLE,
    CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem isDomain_quot_maximalIdeal_of_smooth :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom →
      GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U,
        G.hom y = closedPoint R →
          IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  intro R _ _ G hsm hgc U hU y hyU hy
  haveI := hsm
  haveI := hgc
  let f : G.left ⟶ Spec (CommRingCat.of R) := G.hom
  let g : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (residue R))
  haveI hI : IsIntegral (pullback f g) := GlobalTheory.isIntegral_specialFibre_of_smooth f
  let q := pullback.fst f g
  have H : IsPullback q (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hsurj : Function.Surjective (q.app U).hom :=
    GlobalTheory.SmallExtLift.app_surj (residue_surjective) H hU
  have hker : RingHom.ker (q.app U).hom = (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
    rw [abLawCst_eq_smallExtLiftCst]
    apply le_antisymm
    · intro a ha
      have := GlobalTheory.SmallExtLift.mem_of_app_eq_zero (residue_surjective) H hU a ha
      rwa [ker_residue] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst H.w,
        (residue_eq_zero_iff r).2 hr, map_zero]
  have hne : Nonempty (q ⁻¹ᵁ U) := by
    have hpt : f y = g (closedPoint (ResidueField R)) := by
      rw [show f y = G.hom y from rfl, hy]
      exact (IsLocalRing.comap_closedPoint (residue R)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hpt
    exact ⟨⟨z, show q z ∈ U from hz ▸ hyU⟩⟩
  haveI : IsDomain Γ(pullback f g, q ⁻¹ᵁ U) := inferInstance
  rw [← hker]
  exact (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isDomain

end GlobalTheory
