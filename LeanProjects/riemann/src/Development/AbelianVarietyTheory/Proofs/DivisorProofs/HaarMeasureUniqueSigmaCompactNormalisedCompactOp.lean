import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

theorem haar_unique_of_sigmaCompact_normalised :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  intro G _ _ _ _ _ _ μ ν _ _ _ K hK hcov s c hso hsc hsn hνs
  have key : ∀ A : Set G, IsCompact (closure A) →
      ν A = (Measure.haarScalarFactor ν μ : ENNReal) * μ A := fun A hA => by
    have := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν μ hA
    rw [this, ENNReal.smul_def, smul_eq_mul]
  have hs0 : μ s ≠ 0 := (hso.measure_pos μ hsn).ne'
  have hstop : μ s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : c = (Measure.haarScalarFactor ν μ : ENNReal) := by
    have h1 := key s (hsc.closure_of_subset subset_rfl)
    rw [hνs] at h1
    exact (ENNReal.mul_left_inj hs0 hstop).mp h1
  subst hc
  ext A hA
  let B : ℕ → Set G := fun j => A ∩ Set.accumulate K j
  have hBmono : Monotone B := fun i j hij => Set.inter_subset_inter_right _ (Set.monotone_accumulate hij)
  have hBcl : ∀ j, IsCompact (closure (B j)) := fun j =>
    (isCompact_accumulate (fun i => (hK i).1) j).closure_of_subset Set.inter_subset_right
  have hBU : (⋃ j, B j) = A := by
    simp only [B, ← Set.inter_iUnion, Set.iUnion_accumulate, hcov, Set.inter_univ]
  rw [← hBU, hBmono.measure_iUnion, hBmono.measure_iUnion]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact iSup_congr fun j => key _ (hBcl j)

end GlobalTheory
