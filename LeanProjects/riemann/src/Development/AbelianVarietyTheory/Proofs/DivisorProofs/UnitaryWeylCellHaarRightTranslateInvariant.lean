import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroupStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell

theorem cellU_haar_rightInv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ _ p
  have hS := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hU n k hk hn y hy hw
  haveI : LocallyCompactSpace (cellU y) :=
    (hS.1 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hS.1 0).1.mem_nhds (hS.1 0).2.2.1)
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mulRight p).toMeasurableEquiv
  have he : ∀ u, e u = u * p := fun _ => rfl
  let ν : Measure (cellU y) := μ.map e
  haveI : ν.IsMulLeftInvariant := by
    have : ν = μ.map (fun x => x * p) := rfl
    rw [this]; exact isMulLeftInvariant_map_mul_right p
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    show μ.map e K < ⊤
    rw [e.map_apply]
    exact ((hK.image (Homeomorph.mulRight p).symm.continuous)).measure_lt_top.trans_le' (by
      apply le_of_eq; congr 1; ext x; simp [e, Homeomorph.mulRight, Equiv.mulRight])

  set j : ℕ := depthU k (p : GU σ n)
  have hp : p ∈ shellU k y (j : ℤ) := mem_shellU_depth k y p
  obtain ⟨ho, hc, h1, hmul, hinv⟩ := hS.1 (j : ℤ)
  have hνS : ν (shellU k y j) = 1 * μ (shellU k y j) := by
    rw [one_mul]
    show μ.map e _ = _
    rw [e.map_apply]
    congr 1
    ext u
    simp only [Set.mem_preimage, he]
    constructor
    · intro h
      simpa using hmul _ _ h (hinv p hp)
    · intro h; exact hmul _ _ h hp
  have hνμ : ν = μ := by
    have := GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen (cellU y) μ ν (fun i : ℕ => shellU k y (i : ℤ))
      (fun i => ⟨(hS.1 i).2.1, (hS.1 i).1.measurableSet⟩)
      (Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩)
      _ 1 ho hc ⟨1, h1⟩ hνS
    rwa [one_smul] at this
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, hνμ⟩
  refine ⟨fun F => ?_, fun F => ?_⟩
  · exact hmp.integral_comp' (g := fun u : cellU y => F (u : GU σ n))
  · exact hmp.lintegral_comp_emb e.measurableEmbedding (fun u : cellU y => F (u : GU σ n))

end GlobalTheory.WeylCell.WeylUnipotentShell
