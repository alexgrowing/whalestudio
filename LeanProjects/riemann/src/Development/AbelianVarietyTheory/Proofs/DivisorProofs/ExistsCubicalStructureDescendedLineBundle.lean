import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_cubicalStr_of_descended_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), Nonempty (CubicalStr G (⟨L, rig, hL, hr⟩ : RigLB G)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hgal D D' hD A' G' _ _ hG' U' a G _ _ β hG hβ hact L hL _ rig hr
  obtain ⟨A, gen, -, -, -, -⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hρ hgal D D' hD A' G' hG' U' a G β hG hβ hact
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  have : IsProper (pullback.snd G.hom (jK R)) := by
    have : IsProper A.A.hom := A.isAb.proper
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w gen.hom
    rw [← hw]
    infer_instance
  obtain ⟨L₀, c, rfl⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hG this L hL
  exact ⟨⟨c.t, c.isGen, c.face, c.cubeSymmetric_swap_first, c.cubeSymmetric_swap_last, c.cocycle⟩⟩

end GlobalTheory.Mum
