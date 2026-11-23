import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasis
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodO_adic_complete_compact_basis : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ ϖ : O, Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O ∧ Finite (O ⧸ Ideal.span {ϖ}) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∃ e : ℕ, (l : O) ∈ Ideal.span {ϖ} ∧ ϖ ^ e ∈ Ideal.span {(l : O)}) ∧ (nhds (0 : LL)).HasBasis (fun _ : ℕ => True) (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ) ∧ ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL) := by
  first | exact @GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure | exact GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure | (intros; apply GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure <;> assumption)
