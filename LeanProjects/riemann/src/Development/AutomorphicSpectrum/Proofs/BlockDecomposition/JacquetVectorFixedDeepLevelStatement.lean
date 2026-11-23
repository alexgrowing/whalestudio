import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevel
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_vector_fixed_deep_level : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧ ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd, jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  first | exact @GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth | exact GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth | (intros; apply GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth <;> assumption)
