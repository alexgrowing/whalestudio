import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_functions_period_ring_separation : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∀ x : (A.cont ℤ_[l]).Acr n, IsLocallyConstant fun z => mapAcr (A.evCont z) n x) ∧ (∀ x : (A.cont ℤ_[l]).Acr n, (∀ z, mapAcr (A.evCont z) n x = 0) → x = 0) ∧ ∀ (𝔞 : Ideal ((base l).Acr n)) (f : ℤ_[l] → A.Acr n), IsLocallyConstant f → (∀ z, f z ∈ 𝔞.map (mapAcr A.fromBase n)) → ∃ x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), ∀ z, mapAcr (A.evCont z) n x = f z := by
  first | exact @GlobalTheory.CompanionTheory.ContAcr.acr_cont | exact GlobalTheory.CompanionTheory.ContAcr.acr_cont | (intros; apply GlobalTheory.CompanionTheory.ContAcr.acr_cont <;> assumption)
