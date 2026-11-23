import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealValConjInv
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
theorem _root_.GlobalTheory.T.conjugate_curve_tangent_compat : ∀ (W₀ W₁ : WeierstrassCurve ℂ) (g : ℂ →+* ℂ) (h : W₀.map g = W₁) (c : ℂ), tan W₁ (g c) ≫ mapHom W₀ g h = spMap (Chart.dualMapR g) ≫ tan W₀ c := by
  first | exact @GlobalTheory.CMTorsion.tan_mapHom_conj | exact GlobalTheory.CMTorsion.tan_mapHom_conj | (intros; apply GlobalTheory.CMTorsion.tan_mapHom_conj <;> assumption)
