import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_satake_almost_all : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ, (CG.mk π).HasSat w B := by
  first | exact @GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | exact GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | (intros; apply GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat <;> assumption)
