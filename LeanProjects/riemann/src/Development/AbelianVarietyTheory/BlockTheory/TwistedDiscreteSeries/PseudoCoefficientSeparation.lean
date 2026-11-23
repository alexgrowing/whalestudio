import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn UJset allPos)
open GlobalTheory.Dec (HasInfChar IsSqIntIrr UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

namespace GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

def HasWideGaps {r : ℕ} (lam : Fin r → ℤ) : Prop :=
  StrictAnti lam ∧ ∀ i j : Fin r, (j : ℕ) = i + 1 → (r : ℤ) ≤ lam i - lam j

def IsDiscreteWithInfChar {r : ℕ} (ε : Fin r → Bool) (lam : Fin r → ℤ) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) : Prop :=
  IsSqIntIrr ε D ∧ HasInfChar ε (fun a => (lam a : ℂ)) D

def PseudoCoeffSeparation : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), HasWideGaps lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
      (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) (hD : IsDiscreteWithInfChar ε lam D)
      (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hD.1.2.2.1) f →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : Matrix (Fin r) (Fin r) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 →
        HasInfChar ε (fun a => (lam a : ℂ)) π ∧ (IsURepOn (UJset ε) π → UEquiv ε π D ∧ c = 1)

theorem hasWideGaps_mul (r : ℕ) : HasWideGaps fun i : Fin r => -((r : ℤ) * (i : ℕ)) := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · have h1 : ((i : ℕ) : ℤ) < (j : ℕ) := by exact_mod_cast h
    have h2 : (0 : ℤ) < r := by exact_mod_cast i.pos
    simp only [neg_lt_neg_iff]
    exact mul_lt_mul_of_pos_left h1 h2
  · simp only [h]
    push_cast
    ring_nf
    rfl

example : ¬ HasWideGaps ![1, 0, -1] := fun h => by simpa using h.2 0 1 rfl

theorem exists_data_rank_one (μ : Measure (UJ (allPos 1))) [μ.IsHaarMeasure] :
    HasWideGaps (fun _ : Fin 1 => (0 : ℤ)) ∧
      ∃ hD : IsDiscreteWithInfChar (allPos 1) (fun _ => 0) fun _ => ContinuousLinearMap.id ℂ ℂ,
        ∃ f, IsPseudoCoeff (ujMat (allPos 1)) μ (ujRep hD.1.2.2.1) f ∧
          ∃ hπ : IsIrrAdm (allPos 1) fun _ => ContinuousLinearMap.id ℂ ℂ,
            HasTrace (repOp (groupRep (allPos 1) hπ.2.1.1) μ f) 1 := by
  obtain ⟨h, f, -, hf⟩ := GlobalTheory.Published.pseudoCoefficientUpq_trivial 1 μ
  refine ⟨⟨Subsingleton.strictAnti _, fun i j e => by omega⟩, ⟨h, fun v w _ _ => ?_⟩, f, hf,
    ⟨h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.2, fun _ _ _ => rfl, fun _ => inferInstance⟩, h.2.2.2.1⟩, hf.trace_self⟩
  have := GlobalTheory.Dec.isZEigen_const (allPos 1) (inner ℂ w v)
  convert this using 2 with a
  · simp [Formalism.QuantumDeterminants.rhoStd]
  · rfl

end GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

end
