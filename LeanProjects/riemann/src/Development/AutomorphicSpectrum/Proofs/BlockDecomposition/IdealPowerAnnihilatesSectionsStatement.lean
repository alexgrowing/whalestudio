import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerAnnihilatesSections
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_annihilates_sections : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left) (V : (Y e).left.Opens), I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.pow_smul_top_secOnR | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.pow_smul_top_secOnR | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.pow_smul_top_secOnR <;> assumption)
