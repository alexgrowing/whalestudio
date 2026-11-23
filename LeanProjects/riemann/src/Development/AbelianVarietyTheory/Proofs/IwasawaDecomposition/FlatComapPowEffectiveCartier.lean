import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierComapOfDisjoint
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem effCartier_comap_pow_idealSheaf_of_flat :
    ∀ (X Y : Scheme.{0}) (D : GlobalTheory.EffCartierData X) (g : Y ⟶ X), Flat g → ∀ n : ℕ,
      FinalTheorems.EffCartier ((D.idealSheaf ^ n).comap g) := by
  intro X Y D g hg n
  rw [← D.idealSheaf_nsmul n]
  exact GlobalTheory.TorRef.effCartier_comap_of_flat _ g (D.nsmul n).effCartier_idealSheaf

end GlobalTheory
