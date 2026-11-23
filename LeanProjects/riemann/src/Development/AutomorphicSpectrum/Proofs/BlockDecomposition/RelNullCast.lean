import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AppendCons
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFinsetInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupMemRelS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DCupZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem relNull_cast {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of K))
    {Q : ObjectProperty (Thick (smFun Y q))} {a n c c' N N' : ℕ} (hc : 1 + a = c) (hc' : 1 + a = c') (hN : 2 + n = N)
    (hN' : 2 + n = N') (r : CH.Cn (G q 1) 2) (z : CH.Cn (G q a) n)
    (h : RelNull (G q c) Q N (cupC q (a := 1) (a' := a) hc hN r z)) :
    RelNull (G q c') Q N' (cupC q (a := 1) (a' := a) hc' hN' r z) := by
  subst hc hc' hN hN'
  exact h

theorem relKillOf : TopRes → FormUniq → OmRes → RelKillOf := by
  intro hTop hFU hOR hSL hCD hZR hAO hON hAR hFL hDW hDL hFC hC1 hDC hCK K _ _ W Z Y q _ _ i π _ D d hd hB r hr hc1 a n z hz hzr
  obtain ⟨B⟩ := hB
  haveI := B.closed
  obtain ⟨m, U, σ, hσ, hU, haff, hcov⟩ := hDC K W Z Y q i π D d B
  obtain ⟨-, hQ, -⟩ := hSL K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  exact relNull_cast (π ≫ q) _ _ _ _ r z
    (kill_over hTop hFU hOR hSL hCD hZR hAO hAR hFL hDW hDL hFC hC1 hCK D hQ B.f B.f_nat B.f_u U σ hσ hU haff hcov
      r hr hc1 a n z hz hzr)

end GlobalTheory.CompanionTheory.RelKill
