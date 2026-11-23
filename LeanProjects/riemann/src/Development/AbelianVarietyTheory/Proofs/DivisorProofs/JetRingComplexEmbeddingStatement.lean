import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingComplexEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_complex_embedding : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ := by
  first | exact @GlobalTheory.LatJet.jet_coeffMap | exact GlobalTheory.LatJet.jet_coeffMap | (intros; apply GlobalTheory.LatJet.jet_coeffMap <;> assumption)
