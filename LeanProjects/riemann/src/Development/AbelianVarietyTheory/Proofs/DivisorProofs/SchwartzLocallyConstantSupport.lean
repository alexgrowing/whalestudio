import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section
open Filter Topology

namespace GlobalTheory.SBBounds

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tendsto_pow_zero {x : k} (h : valuation k x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem sb_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ φ : Matrix (Fin n) (Fin n) k → ℂ, φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ N M : ℕ, (∀ X, φ X ≠ 0 → t ^ N • X ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X E, E ∈ intM k (Fin n) (Fin n) → φ (X + t ^ M • E) = φ X := by
  intro k _ _ _ _ n t _ ht φ hφ
  obtain ⟨hlc, hcs⟩ := hφ
  have hU : IsOpen (intM k (Fin n) (Fin n)) := isOpen_intMatrix
  have hUc : IsCompact (intM k (Fin n) (Fin n)) := isCompact_intMatrix
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).zero_mem
  have htO : t ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hT := tendsto_pow_zero ht

  have hmono : Monotone fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)} := by
    intro N N' hNN' X hX i j
    have e : t ^ N' • X = t ^ (N' - N) • (t ^ N • X) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hNN']
    rw [e]
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (𝒪[k]).mul_mem ((𝒪[k]).pow_mem htO _) (hX i j)
  obtain ⟨N, hN⟩ := hcs.isCompact.elim_directed_cover
    (fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)})
    (fun N => hU.preimage (f := fun X : Matrix (Fin n) (Fin n) k => t ^ N • X) (continuous_const_smul _))
    (fun X _ => by
      have h1 : Tendsto (fun N : ℕ => t ^ N • X) atTop (𝓝 ((0 : k) • X)) := hT.smul_const X
      rw [zero_smul] at h1
      obtain ⟨N, hN⟩ := (h1.eventually (hU.mem_nhds h0)).exists
      exact Set.mem_iUnion.2 ⟨N, hN⟩)
    hmono.directed_le

  have hZ : IsOpen {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by
    have c1 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k =>
        p.2.1 + p.1 • p.2.2 := by fun_prop
    have c2 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.2.1 := by fun_prop
    have := ((hlc.comp_continuous c1).comp₂ (hlc.comp_continuous c2) fun a b => a - b).isOpen_fiber 0
    simpa [Function.comp_def, sub_eq_zero] using this
  have hKU : IsCompact (tsupport φ ×ˢ intM k (Fin n) (Fin n)) := hcs.isCompact.prod hUc
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ q ∈ tsupport φ ×ˢ intM k (Fin n) (Fin n), φ (q.1 + c • q.2) = φ q.1 := by
    refine hKU.eventually_forall_of_forall_eventually fun q _ => ?_
    have hm : ((0 : k), q) ∈ {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by simp
    exact hZ.mem_nhds hm
  obtain ⟨M, hM⟩ := (hT.eventually hev).exists
  refine ⟨N, M, fun X hX => hN (subset_tsupport _ hX), fun X E hE => ?_⟩
  by_cases hX : X ∈ tsupport φ
  · exact hM (X, E) ⟨hX, hE⟩
  by_cases hX' : X + t ^ M • E ∈ tsupport φ
  · have hE' : -E ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).neg_mem (hE i j)
    have := hM (X + t ^ M • E, -E) ⟨hX', hE'⟩
    simp only [smul_neg, add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

end GlobalTheory.SBBounds
