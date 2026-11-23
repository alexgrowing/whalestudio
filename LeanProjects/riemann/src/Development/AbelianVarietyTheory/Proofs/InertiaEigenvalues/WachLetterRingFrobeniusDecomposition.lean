import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiDec

theorem phi_dec : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  intro D HW l _ K s LL h W a
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  choose z hz using fun i : Let K => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (a i)).exists
  refine ⟨fun j i => z (i + 1) j, ?_⟩
  funext i
  rw [Finset.sum_apply]
  have hi : a i = a (i - 1 + 1) := by rw [sub_add_cancel]
  rw [hi, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show _ = _ * ((HW l).W K s LL h).φ₀ _
  rw [hφ]

end GlobalTheory.NL.PhiDec
