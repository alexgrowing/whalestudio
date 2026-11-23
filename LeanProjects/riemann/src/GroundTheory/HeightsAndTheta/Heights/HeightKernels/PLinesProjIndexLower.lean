import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace KLinesProjIndexLower

theorem stdLattice_fg (K : Type) [Field K] [NumberField K] (k : ℕ) :
    ((stdLattice K k).restrictScalars ℤ).FG :=
  (Submodule.fg_span (Set.finite_range _)).restrictScalars

theorem stdLattice_span (K : Type) [Field K] [NumberField K] (k : ℕ) :
    Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ :=
  (HermLattice.standard K k).span_eq

end KLinesProjIndexLower

open KLinesProjIndexLower in

theorem LinesProjIndexLower.proof (h1 : LinesProjLattice.Statement)
    (h2 : LinesIdealLatticeFG.Statement) (h3 : LinesIsLattice.Statement)
    (h4 : LinesGenIndexMono.Statement) (h5 : LinesIdealStdIndex.Statement) :
    LinesProjIndexLower.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hPfg, hPspan, hle⟩ := h1 K n m k a B τ ha hB hτ
  obtain ⟨hAfg, hAspan⟩ := h2 K k (fun j => a (τ j)) (fun j => ha (τ j))
  have hA := h3 K (Fin k) _ hAfg.restrictScalars hAspan
  have hP := h3 K (Fin k) _ hPfg hPspan
  have hS := h3 K (Fin k) _ (stdLattice_fg K k) (stdLattice_span K k)
  have key := h4 (Fin k → K) _ _ _ hA hP hS (Submodule.restrictScalars_mono ℤ hle)
  rw [← h5 K k (fun j => a (τ j))]
  exact key

end

end GroundTheory.Heights₂.Heights
