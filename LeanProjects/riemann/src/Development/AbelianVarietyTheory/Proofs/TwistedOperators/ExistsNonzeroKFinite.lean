import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KFinExists

theorem exists_kfin (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [Nontrivial V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (hπ : IsURepOn (UJset ε) π) : ∃ v, IsKFin ε π v ∧ v ≠ 0 := by
  obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hπ
  have hmem : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ UJset ε := fun k => (k : Formalism.REAL.UJ ε).2
  have hone : Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 := rfl
  have hmk : ∀ a b : Formalism.REAL.KG ε, Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b :=
    fun _ _ => rfl
  let ρ : Formalism.REAL.KG ε →* (V →L[ℂ] V) :=
    { toFun := fun k => π (Formalism.REAL.toMK k)
      map_one' := by simp only [hone, h1]
      map_mul' := fun a b => by
        simp only [hmk]
        exact hmul _ (hmem a) _ (hmem b) }
  have hcK : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨S, hS0, hSfd, hSinv⟩ := GlobalTheory.T.compact_unitary_finite_invariant_subspace (Formalism.REAL.KG ε) V ρ
    (fun k x => hnorm _ (hmem k) x)
    (fun x => (hcont x).comp_continuous hcK hmem)
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine ⟨v, ⟨S, hSfd, hvS, ?_⟩, hv0⟩
  intro g hg x hx
  have hr : g ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
    rw [Formalism.REAL.range_toMK]; exact hg
  obtain ⟨k, rfl⟩ := hr
  exact hSinv k x hx

end GlobalTheory.KFinExists
