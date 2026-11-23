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

namespace GlobalTheory.RepsCard

theorem card_reps_eq : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SA SB : Finset V, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA → Formalism.L2.Th1.H.IsReps Λ B SB → SA.card = SB.card := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, h5⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hone : ∀ {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (c : ℂ), Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S →
      ∑ x ∈ S, (if x ∈ Λ₁ then c else 0) = c := by
    intro Λ₁ Λ₂ S c hS
    obtain ⟨x₀, hx₀, hd⟩ := hS.2.2 0 Λ₂.zero_mem
    have hx₀Λ : x₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hd
    rw [Finset.sum_eq_single x₀]
    · simp [hx₀Λ]
    · intro x hx hne
      rw [if_neg]
      intro hxΛ
      exact hne (hS.2.1 x hx x₀ hx₀ (Λ₁.sub_mem hxΛ hx₀Λ))
    · intro h; exact absurd hx₀ h
  have hcol : ∀ s ∈ SA, ∑ y ∈ SB, brk H y s = if s ∈ B then (SB.card : ℂ) else 0 := by
    intro s hs
    have hsΛ : s ∈ Λ := (hSA.1 s hs).1
    split_ifs with hsB
    · have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hsB
      rw [Finset.sum_congr rfl fun y hy => brk_one_of_int H (hsd y (hSB.1 y hy))]
      simp
    · by_contra hne
      apply hsB
      have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by
        intro y hyB
        by_contra hno
        refine hne (char_sum_zero hSB (fun y => brk H y s) (fun u v => brk_add_left H u v s) ?_ (x₀ := y) hyB ?_)
        · intro m _ hmΛ; exact brk_one_of_int H (hΛint hsΛ m hmΛ)
        · intro h1; exact hno (int_of_brk_one H h1)
      rwa [sdB] at hsd
  have hrow : ∀ y ∈ SB, ∑ s ∈ SA, brk H y s = if y ∈ Λ then (SA.card : ℂ) else 0 := by
    intro y hy
    have hyB : y ∈ B := hSB.1 y hy
    split_ifs with hyΛ
    · rw [Finset.sum_congr rfl fun s hs => brk_one_of_int H (hΛint (hSA.1 s hs).1 y hyΛ)]
      simp
    · by_contra hne
      apply hyΛ
      apply h5 y hyB
      intro a haA haΛ
      by_contra hno
      refine hne (char_sum_zero hSA (fun s => brk H y s) (fun u v => brk_add_right H y u v) ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro m _ hmB; exact brk_one_of_int H (hBint hmB y hyB)
      · intro h1; exact hno (int_of_brk_one H h1)
  have key : ∑ s ∈ SA, ∑ y ∈ SB, brk H y s = ∑ y ∈ SB, ∑ s ∈ SA, brk H y s := Finset.sum_comm
  rw [Finset.sum_congr rfl hcol, Finset.sum_congr rfl hrow, hone _ hSA, hone _ hSB] at key
  exact_mod_cast key.symm

end GlobalTheory.RepsCard
