import Mathlib

open scoped SchwartzMap ContDiff Topology Uniformity
open Filter

namespace GlobalTheory.CompanionTheory.SchwartzBaire

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_sub_apply' (f g : 𝓢(E, F)) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (⇑(f - g)) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x := by
  have h : (⇑(f - g) : E → F) = ⇑f - ⇑g := by
    ext x
    simp
  rw [h]
  exact iteratedFDeriv_sub_apply (f.smooth l).contDiffAt (g.smooth l).contDiffAt

theorem cauchy_weighted (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖ ≤ ε := by
  have h0 := hf.tendsto_uniformity
  rw [uniformity_eq_comap_nhds_zero 𝓢(E, F), tendsto_comap_iff] at h0
  have h1 := ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ 0).1 h0 (k, l) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h1
  refine ⟨max N₁ N₂, fun m hm m' hm' x => ?_⟩
  have hmm := hN (m', m) ⟨le_trans (le_max_left _ _) hm', le_trans (le_max_right _ _) hm⟩
  simp only [Function.comp_apply, Prod.map_apply, sub_zero] at hmm
  rw [← iteratedFDeriv_sub_apply']
  exact (SchwartzMap.le_seminorm ℝ k l (f m - f m') x).trans hmm.le

theorem exists_tendsto [CompleteSpace F] (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) :
    ∃ g : 𝓢(E, F), Tendsto f atTop (𝓝 g) := by
  have hpt : ∀ l x, CauchySeq (fun n => iteratedFDeriv ℝ l (f n) x) := by
    intro l x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_weighted f hf 0 l (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn N le_rfl x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm]
    linarith
  choose G hG using fun l x => cauchySeq_tendsto_of_complete (hpt l x)
  have hlim : ∀ k l {δ : ℝ}, 0 < δ → ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖ ≤ δ := by
    intro k l δ hδ
    obtain ⟨N, hN⟩ := cauchy_weighted f hf k l hδ
    refine ⟨N, fun m hm x => ?_⟩
    have ht : Tendsto (fun m' => ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖)) :=
      ((tendsto_const_nhds.sub (hG l x)).norm).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m' hm' => hN m hm m' hm' x⟩)
  have hunif : ∀ l, TendstoUniformly (fun n x => iteratedFDeriv ℝ l (f n) x) (G l) atTop := by
    intro l
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlim 0 l (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h := hN n hn x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  let g₀ : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x l => G l x
  have hT : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) g₀ p := by
    refine ⟨fun x => rfl, fun m _ x => ?_, fun m _ => ?_⟩
    · have hU : TendstoUniformly (fun n y => (iteratedFDeriv ℝ (m + 1) (f n) y).curryLeft)
          (fun y => (G (m + 1) y).curryLeft) atTop :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hunif (m + 1))
      exact hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ m (f n) y) hU
        (fun n y => ((f n).smooth ⊤).ftaylorSeries.fderiv m (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)) y)
        (fun y => hG m y) x
    · exact (hunif m).continuous (Frequently.of_forall fun n => ((f n).smooth m).continuous_iteratedFDeriv le_rfl)
  have hg : ∀ l x, iteratedFDeriv ℝ l g₀ x = G l x := fun l x =>
    (hT.eq_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) x).symm
  have hdecay : ∀ k l : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l g₀ x‖ ≤ C := by
    intro k l
    obtain ⟨N, hN⟩ := hlim k l one_pos
    refine ⟨1 + SchwartzMap.seminorm ℝ k l (f N), fun x => ?_⟩
    rw [hg]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k l (f N) x
    have h3 : ‖G l x‖ ≤ ‖iteratedFDeriv ℝ l (f N) x‖ + ‖iteratedFDeriv ℝ l (f N) x - G l x‖ := by
      calc ‖G l x‖ = ‖iteratedFDeriv ℝ l (f N) x - (iteratedFDeriv ℝ l (f N) x - G l x)‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hxk : 0 ≤ ‖x‖ ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hxk]
  let g : 𝓢(E, F) := ⟨g₀, hT.contDiff, hdecay⟩
  have hcoe : (⇑g : E → F) = g₀ := rfl
  refine ⟨g, ?_⟩
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds _ _]
  intro i ε hε
  obtain ⟨N, hN⟩ := hlim i.1 i.2 (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hb : SchwartzMap.seminorm ℝ i.1 i.2 (f m - g) ≤ ε / 2 :=
    SchwartzMap.seminorm_le_bound ℝ i.1 i.2 _ (by positivity) fun x => by
      rw [iteratedFDeriv_sub_apply', hcoe, hg]
      exact hN m hm x
  exact lt_of_le_of_lt hb (half_lt_self hε)

theorem completeSpace [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun f hf => exists_tendsto f hf

theorem baireSpace [CompleteSpace F] : BaireSpace 𝓢(E, F) := by
  have : CompleteSpace 𝓢(E, F) := completeSpace
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory.CompanionTheory.SchwartzBaire
