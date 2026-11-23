import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPoint_eq_of_deco_and_cosetReduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | exact GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | (intros; apply GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar <;> assumption)
