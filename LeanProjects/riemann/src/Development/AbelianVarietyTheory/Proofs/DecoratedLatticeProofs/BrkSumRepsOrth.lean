import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem brk_sum_reps_orth : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SB : Finset V, Formalism.L2.Th1.H.IsReps Λ B SB → ∀ w ∈ Λ ⊓ A, ∑ y ∈ SB, brk H y w = if w ∈ B then (SB.card : ℂ) else 0 := by
  intro V _ _ H α A B Λ hyp SB hSB w hw
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, -⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hwΛ : w ∈ Λ := (AddSubgroup.mem_inf.1 hw).1
  by_cases hwB : w ∈ B
  · rw [if_pos hwB, Finset.sum_congr rfl fun y hy => brk_one_of_int H (hBint hwB y (hSB.1 y hy))]
    simp
  · rw [if_neg hwB]
    have hnd : w ∉ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hwB
    have hex : ∃ y₀ ∈ B, ¬ ∃ m : ℤ, Formalism.L2.Th1.H.altE H w y₀ = (m : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hnd (fun y hy => hcon y hy)
    obtain ⟨y₀, hy₀B, hy₀⟩ := hex
    exact char_sum_zero hSB (fun y => brk H y w) (fun u v => brk_add_left H u v w)
      (fun m _ hmΛ => brk_one_of_int H (hΛint hwΛ m hmΛ)) (x₀ := y₀) hy₀B
      (fun h => hy₀ (int_of_brk_one H h))

end GlobalTheory
