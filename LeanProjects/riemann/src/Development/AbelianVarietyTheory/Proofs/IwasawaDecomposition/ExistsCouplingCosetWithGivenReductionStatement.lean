import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_couplingCoset_with_given_reduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (q : PtAt R sel mu cst u j) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs), ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq | exact GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq | (intros; apply GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq <;> assumption)
