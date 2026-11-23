import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_base_change_from_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.AcrMod.acr_modp | exact GlobalTheory.CompanionTheory.AcrMod.acr_modp | (intros; apply GlobalTheory.CompanionTheory.AcrMod.acr_modp <;> assumption)
