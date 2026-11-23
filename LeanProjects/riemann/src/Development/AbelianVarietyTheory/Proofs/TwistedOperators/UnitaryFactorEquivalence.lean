import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerNonzeroOnGeneratingSetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedIntertwinerSchurStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.UnitaryFromModules

theorem uEquiv_of_isFactor : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε ρ → IsURepOn (UJset ε) ρ → IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ Z, IsFactor ε ρ Z (kFinVec ε ρ) π → UEquiv ε π ρ := by
  intro hHC n ε H _ _ _ ρ V _ _ _ π hρ hρU hπ hπU Z hF
  obtain ⟨-, hY, -, T, hmap, -, hK, hL⟩ := hF
  haveI : Nontrivial V := hπ.1
  obtain ⟨w, hwK, hw0⟩ := GlobalTheory.T.exists_nonzero_k_finite n ε V π hπU
  have hw : w ∈ (kFinVec ε ρ).map T := hmap ▸ hwK
  obtain ⟨y₀, hy₀, rfl⟩ := hw
  have hTK : ∀ y, IsKFin ε ρ y → IsKFin ε π (T y) := fun y hy =>
    (hmap ▸ Submodule.mem_map_of_mem (f := T) (show y ∈ kFinVec ε ρ from hy) : T y ∈ kFinVec ε π)
  obtain ⟨a₀, ha₀, hrz⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε H ρ V π hρ.2.1 hπ.2.1 T hmap
    (fun k hk y hy => hK k hk y hy)).2 (T y₀) hwK
  have hsm := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπU hπ.2.2).2
  have hco := GlobalTheory.T.smooth_intertwiner_extension hHC n ε H ρ V π hρ.2.1 hπ.2.1 hY hsm T hTK (fun k hk y hy => hK k hk y hy)
    (fun X hX y hy => hL X hX y hy) a₀ (T y₀) ha₀ hwK hrz
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.intertwiner_nonzero_on_generating_set n ε H ρ V π hρU hρ.2.2 hπU T {y | IsKFin ε ρ y} y₀ a₀ hy₀ hw0 hco
  exact GlobalTheory.T.bounded_intertwiner_schur n ε H ρ V π hρU hρ.2.2 hπU hπ.2.2 B hB0 hB

end GlobalTheory.UnitaryFromModules

end
