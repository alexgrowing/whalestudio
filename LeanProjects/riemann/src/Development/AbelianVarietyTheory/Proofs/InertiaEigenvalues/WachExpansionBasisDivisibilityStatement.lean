import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansion_basis_divisibility : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → (∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x)) ∧ ∀ (r : ℕ) (nb : Module.Basis (Fin r) (AA K LL) ↥(W.N T)), (∀ e : Fin r → PowerSeries ↥LL.1, ∑ j, conv (e j) (ex C h T i ζ (nb j)) = 0 → e = 0) ∧ (∀ f ∈ Lat C h T i ζ, ∃ e : Fin r → PowerSeries ↥LL.1, f = ∑ j, conv (e j) (ex C h T i ζ (nb j))) ∧ ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ y j = f (j - k)) ↔ ∀ j, nb.repr y j ∈ van W i ζ k := by
  first | exact @GlobalTheory.NL.LevInj.expansion_basis | exact GlobalTheory.NL.LevInj.expansion_basis | (intros; apply GlobalTheory.NL.LevInj.expansion_basis <;> assumption)
