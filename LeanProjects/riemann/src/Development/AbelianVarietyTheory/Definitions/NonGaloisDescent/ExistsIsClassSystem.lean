import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem Frame.Good.posDef {F : Frame S T} (h : F.Good) (τ : D.what₂.Tau) : (gramAt D S τ).PosDef := by
  have := (GlobalTheory.GalLift.Vec.isCartanInv_one (h.onbS τ)).2.2
  rwa [Matrix.mul_one] at this

theorem exists_isClassSystem (B : Base S T) (hF : B.F.Good) (ψ : Twist D Circle) :
    ∃ (m : ℕ) (h : Fin m → GA D S), IsClassSystem S (B.levJ ψ) h := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover S hF.posDef (B.levJ ψ)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev S B.F.βS (B.levS ψ))
  have hl : ∀ x : Bridge.Gf S, ∃ k ∈ GfC S, finPt S k = x := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk, e⟩ := GlobalTheory.LevelOpen.exists_finPart D S g
    exact ⟨k, hk, Subtype.ext e⟩
  choose l hl1 hl2 using hl
  have hr : Equivalence fun g g' : Bridge.Gf S => ∃ (γ : GQ S) (k : B.levJ ψ), g = Bridge.ratF S γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr c
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.ParahoricCompact.exists_compact_entries B.F.βS
  refine ⟨n, fun a => l (c (f a)), fun a => hl1 _, fun g => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := hc g
    simp only [hl2]
    exact hf g a ha
  · exact GlobalTheory.RepsObj.finite_stab S hF.posDef _ hC (fun k hk => hCe k.1 (Base.mem_St_of_mem_levJ hk)) _

end GlobalTheory.ExportSeries

end
