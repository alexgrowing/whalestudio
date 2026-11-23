import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem ts_inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hg, hh]

theorem ts_herm_conjTranspose (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring

theorem ts_inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hb]

theorem ts_continuous_herm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  unfold herm
  fun_prop

theorem ts_continuous_nU : Continuous (nU : Matrix (Fin n) (Fin n) ℂ → M2 n) := by
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

set_option maxHeartbeats 1000000 in
theorem twoSided : TwoSided := by
  intro n H F Γ hF hΓ hcl hperm ψ hψc hψs hvan h a b ha hb
  have : FirstCountableTopology (M2 n) :=
    inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  obtain ⟨γ, hγΓ, hγa⟩ := mem_closure_iff_seq_limit.1 (hcl ha)
  have hmap : Continuous (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) :=
    (continuous_fst.mul (ts_continuous_nU.comp (ts_continuous_herm.comp continuous_snd))).mul continuous_const
  have hmem : ∀ c x, InG c → InG (c * nU (herm x) * b) := fun c x hc =>
    ts_inG_mul (ts_inG_mul hc (ts_inG_nU (ts_herm_conjTranspose x))) hb
  have hΦc : ∀ c, InG c → Continuous (fun x => F h (c * nU (herm x) * b)) := by
    intro c hc
    have hcx : Continuous (fun x : Fin n → Fin n → ℝ => c * nU (herm x) * b) :=
      (continuous_const.mul (ts_continuous_nU.comp ts_continuous_herm)).mul continuous_const
    exact (hF h).comp_continuous hcx fun x => hmem c x hc
  have hzero : ∀ k, ∫ x, F h (γ k * nU (herm x) * b) * ψ x = 0 := by
    intro k
    obtain ⟨h', hh'⟩ := hperm (γ k) (hγΓ k) h
    have e : ∀ x, F h (γ k * nU (herm x) * b) * ψ x = F h' (nU (herm x) * b) * ψ x := by
      intro x
      rw [Matrix.mul_assoc, hh' _ (ts_inG_mul (ts_inG_nU (ts_herm_conjTranspose x)) hb)]
    simp_rw [e]
    exact hvan h' b hb
  have hS : IsCompact (insert a (Set.range γ)) := hγa.isCompact_insert_range
  have hSG : insert a (Set.range γ) ⊆ {g | InG g} := by
    rintro c (rfl | ⟨k, rfl⟩)
    · exact ha
    · exact hΓ _ (hγΓ k)
  have hC : IsCompact ((fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ)) := (hS.prod hψs).image hmap
  have hCG : (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ) ⊆ {g | InG g} := by
    rintro _ ⟨⟨c, x⟩, ⟨hc, -⟩, rfl⟩
    exact hmem c x (hSG hc)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn ((hF h).mono hCG)
  have hbound : ∀ c ∈ insert a (Set.range γ), ∀ x, ‖F h (c * nU (herm x) * b) * ψ x‖ ≤ M * ‖ψ x‖ := by
    intro c hc x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hM _ ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hlim : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop
      (𝓝 (∫ x, F h (a * nU (herm x) * b) * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * ‖ψ x‖) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((hΦc _ (hΓ _ (hγΓ k))).mul hψc).aestronglyMeasurable
    · exact (hψc.norm.integrable_of_hasCompactSupport hψs.norm).const_mul M
    · exact Eventually.of_forall fun x => hbound _ (Set.mem_insert_of_mem _ ⟨k, rfl⟩) x
    · refine Eventually.of_forall fun x => ?_
      refine Tendsto.mul_const _ ?_
      have hw : ContinuousWithinAt (F h) {g | InG g} (a * nU (herm x) * b) := hF h _ (hmem a x ha)
      refine hw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hmem _ x (hΓ _ (hγΓ k))⟩)
      exact ((hγa.mul tendsto_const_nhds).mul tendsto_const_nhds)
  have h0 : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop (𝓝 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

end PositivityTheory.Rg.Sw.LVs
