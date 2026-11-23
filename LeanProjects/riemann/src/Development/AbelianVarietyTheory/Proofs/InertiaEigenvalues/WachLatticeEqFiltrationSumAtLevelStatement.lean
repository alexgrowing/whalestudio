import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_eq_filtration_sum_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, f ∈ Lat C h T i ζ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k : ℤ, f k ∈ Di (HW l) h T i ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (f k) ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
  first | exact @GlobalTheory.NL.LatFil.lat_eq_fil | exact GlobalTheory.NL.LatFil.lat_eq_fil | (intros; apply GlobalTheory.NL.LatFil.lat_eq_fil <;> assumption)
