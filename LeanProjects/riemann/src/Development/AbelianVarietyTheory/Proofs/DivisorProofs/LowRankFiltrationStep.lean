import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem mem_lowRank_succ_sup_twistSpan_of_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r hr Φ hΦ
  obtain ⟨⟨hlc, hcs⟩, hvan⟩ := hΦ
  classical

  have hSclosed : IsClosed {X : Matrix A D k | Φ X ≠ 0} := by
    have : {X : Matrix A D k | Φ X ≠ 0} = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hlc.isOpen_fiber 0).isClosed_compl
  have hScpt : IsCompact {X : Matrix A D k | Φ X ≠ 0} :=
    hcs.isCompact.of_isClosed_subset hSclosed (fun X hX => subset_tsupport Φ hX)

  let m₀ : Matrix A D k → ℕ := fun X =>
    if h : X.rank = r then Classical.choose (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr) else 0
  have hm₀ : ∀ X : Matrix A D k, ∀ h : X.rank = r, ∀ m ≥ m₀ X, ∀ C ∈ box ϖ X (fun _ => m₀ X),
      boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    intro X h
    have := Classical.choose_spec (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr)
    simpa [m₀, h] using this
  let U : Matrix A D k → Set (Matrix A D k) := fun X =>
    if X.rank ≤ r then box ϖ X (fun _ => m₀ X) else {Y | r + 1 ≤ Y.rank}
  have hU : ∀ X ∈ {X : Matrix A D k | Φ X ≠ 0}, U X ∈ nhds X := by
    intro X _
    by_cases h : X.rank ≤ r
    · simp only [U, h, if_true]
      refine (isClopen_box ϖ X _).isOpen.mem_nhds ?_
      intro i j; simp
    · simp only [U, h, if_false]
      exact (GlobalTheory.T.isOpen_rank_ge k A D (r + 1)).mem_nhds (by simp only [Set.mem_setOf_eq]; omega)
  obtain ⟨t, htS, hcover⟩ := hScpt.elim_nhds_subcover U hU
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.schwartz_bruhat_box_decomposition k A D ϖ hϖ Φ ⟨hlc, hcs⟩
  obtain ⟨s, hdec, hconst⟩ := hm₁ (max m₁ (t.sup m₀)) (le_max_left _ _)
  set m := max m₁ (t.sup m₀) with hm
  rw [hdec]
  refine Submodule.sum_mem _ fun c hc => ?_
  by_cases hex : ∃ X₂ ∈ box ϖ c (fun _ => m), X₂.rank ≤ r
  · obtain ⟨X₂, hX₂, hX₂r⟩ := hex
    by_cases hc0 : Φ c = 0
    · rw [hc0, zero_smul]; exact zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hX₂S : Φ X₂ ≠ 0 := by rw [hconst c hc X₂ hX₂]; exact hc0
    have hX₂eq : X₂.rank = r := by
      by_contra hne
      exact hX₂S (hvan X₂ (lt_of_le_of_ne hX₂r hne))
    obtain ⟨x, hxt, hxU⟩ := Set.mem_iUnion₂.1 (hcover hX₂S)
    have hxS : Φ x ≠ 0 := htS x hxt
    by_cases hxr : x.rank ≤ r
    · simp only [U, hxr, if_true] at hxU
      have hxeq : x.rank = r := by
        by_contra hne
        exact hxS (hvan x (lt_of_le_of_ne hxr hne))
      have hmx : m₀ x ≤ m := le_trans (Finset.le_sup (f := m₀) hxt) (le_max_right _ _)
      rw [← boxFn_eq_of_mem hX₂]
      exact hm₀ x hxeq m hmx X₂ hxU
    · simp only [U, hxr, if_false, Set.mem_setOf_eq] at hxU
      omega
  · push_neg at hex
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_)
    refine ⟨boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
    have hYn : Y ∉ box ϖ c (fun _ => m) := fun hYb => by
      have := hex Y hYb; omega
    simp [boxFn, Set.indicator_of_notMem hYn]

end GlobalTheory.RankCoinv
