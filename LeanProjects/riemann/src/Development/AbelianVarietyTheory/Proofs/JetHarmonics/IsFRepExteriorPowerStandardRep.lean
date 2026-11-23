import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetPropertiesStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeFRep

theorem entry_le_hs {k r : ℕ} (g : Mx k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem isFRep_cmp (k r l : ℕ) :
    IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  have hm : ∀ g h : Mx k r, cmp l (g * h) = cmp l g * cmp l h := fun g h => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g h).1
  have hc : ∀ g : Mx k r, cmp l gᴴ = (cmp l g)ᴴ := fun g => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g g).2.1
  have h1 : cmp l (1 : Mx k r) = 1 := (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l 1 1).2.2.1
  refine ⟨?_, ?_, h1, fun g _ h _ => hm g h, ?_, ?_, ⟨(l.factorial : ℝ), ?_⟩, ?_⟩
  · rw [← hc, PI.StabPairsW.hpk_conjTranspose]
  · rw [← hm, PI.StabPairsW.hpk_mul_self, h1]
  · intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [← hc, ← hm, ← hm, hg']
  · intro I J
    apply Continuous.continuousOn
    unfold BranchingSupport.cmp
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · intro g _ I J
    have := Matrix.det_le (A := g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2))
      (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (x := B.gN g) (fun i j => entry_le_hs g _ _)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · intro g _ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← hc, ← hm, hu, h1]

end GlobalTheory.WedgeFRep
