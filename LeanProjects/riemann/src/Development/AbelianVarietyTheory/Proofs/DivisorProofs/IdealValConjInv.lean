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

noncomputable section

namespace GlobalTheory.CMTorsion

theorem tan_mapHom_conj (W₀ W₁ : WeierstrassCurve ℂ) (g : ℂ →+* ℂ) (h : W₀.map g = W₁) (c : ℂ) :
    tan W₁ (g c) ≫ mapHom W₀ g h = spMap (Chart.dualMapR g) ≫ tan W₀ c := by
  unfold tan
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  apply GlobalTheory.WeierstrassCurve.ptHom_congr
  · ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · funext i
    fin_cases i
    · show g c • DualNumber.eps = Chart.dualMapR g (c • DualNumber.eps)
      ext <;> simp [Chart.dualMapR]
    · show (-1 : DualNumber ℂ) = Chart.dualMapR g (-1)
      simp
    · show (0 : DualNumber ℂ) = Chart.dualMapR g 0
      simp

end GlobalTheory.CMTorsion

end
