import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
