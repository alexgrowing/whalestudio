import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticSectionFromUniformization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_section_from_uniformization : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ x : Sp ℂ ⟶ scheme (curve Λ Ω), x ≫ toSpec (curve Λ Ω) = 𝟙 _ → ∃ z : ℂ, pt Λ Ω z = x := by
  first | exact @GlobalTheory.CMTorsion.exists_pt_eq | exact GlobalTheory.CMTorsion.exists_pt_eq | (intros; apply GlobalTheory.CMTorsion.exists_pt_eq <;> assumption)
