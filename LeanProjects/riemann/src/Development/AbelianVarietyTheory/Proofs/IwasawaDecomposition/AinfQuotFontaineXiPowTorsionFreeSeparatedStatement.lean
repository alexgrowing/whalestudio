import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfQuotFontaineXiPowTorsionFreeSeparated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_quot_fontaineXi_pow_torsionFree_separated : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  first | exact @GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep | exact GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep | (intros; apply GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep <;> assumption)
