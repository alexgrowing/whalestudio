import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg.Stalk

theorem regular_along_dominant : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i hd hc
  refine ⟨fun p a ha => ?_, fun p a ha hu => ?_, fun z a r hz hv => ?_⟩
  · obtain ⟨hh, h1, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h1 a ha
  · obtain ⟨hh, -, h2⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h2 hc a ha hu
  · obtain ⟨h0, s, hs1, hs2⟩ := hv
    refine ⟨hz, (Scheme.Hom.stalkMap h (centre z)).hom s, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.RegAtDom.genMap_stalkMap hd (centre z) hz h0 s]
      exact congrArg i hs1
    · rw [Scheme.stalkClosedPointTo_comp] at hs2
      rw [← hs2]
      rfl

end GlobalTheory.CompanionTheory.Ar.Chg.Stalk
