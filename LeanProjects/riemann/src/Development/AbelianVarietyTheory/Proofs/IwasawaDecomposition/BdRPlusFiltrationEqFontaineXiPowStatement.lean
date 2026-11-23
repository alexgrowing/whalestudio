import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧ (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧ IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧ (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  first | exact @GlobalTheory.MemLoc.filtration_eq_xi_pow | exact GlobalTheory.MemLoc.filtration_eq_xi_pow | (intros; apply GlobalTheory.MemLoc.filtration_eq_xi_pow <;> assumption)
