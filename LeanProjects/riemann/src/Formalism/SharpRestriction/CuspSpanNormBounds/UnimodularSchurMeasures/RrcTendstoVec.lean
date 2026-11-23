import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace

section Cont

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H] in
theorem rrc_inner (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (a b : H) : ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hn g⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H] in
theorem rrc_bound (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (v u : H) : ‖⟪π g v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := by
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [hn]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H] [Group G] in
theorem rrc_aesm (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (v u : H) :
    AEStronglyMeasurable (fun g => ⟪π g v, u⟫_ℂ) μ := by
  have h := Complex.continuous_conj.comp_aestronglyMeasurable (hm u v)
  refine h.congr (Eventually.of_forall fun g => ?_)
  exact inner_conj_symm _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem rrc_intOn (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v u : H) : IntegrableOn (fun g => ⟪π g v, u⟫_ℂ) k μ :=
  IntegrableOn.of_bound hk (rrc_aesm hm v u).restrict (‖v‖ * ‖u‖) (Eventually.of_forall fun g => rrc_bound hn g v u)

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] in

theorem rrc_exists_vec (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v : H) : ∃ w : H, ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ := by
  have hint := fun u => rrc_intOn hn hm hk v u
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  have hb : ∀ u, ‖L u‖ ≤ (‖v‖ * μ.real k) * ‖u‖ := fun u => by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) hk (fun g _ => rrc_bound hn g v u)
    calc ‖L u‖ ≤ ‖v‖ * ‖u‖ * μ.real k := this
      _ = (‖v‖ * μ.real k) * ‖u‖ := by ring
  refine ⟨(InnerProductSpace.toDual ℂ H).symm (L.mkContinuous _ hb), fun u => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [CompleteSpace H] in
theorem rrc_translate (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    {k : Set G} {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) (u : H) :
    ⟪π h w, u⟫_ℂ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := by
  have e1 : π h (π h⁻¹ u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
  have e2 : ∀ g, ⟪π g v, π h⁻¹ u⟫_ℂ = ⟪π (h * g) v, u⟫_ℂ := fun g => by
    rw [← rrc_inner hn h, e1, hmul]; rfl
  have e3 : (fun g => h * g) ⁻¹' (h • k) = k := by
    ext g; simp [Set.mem_smul_set_iff_inv_smul_mem]
  have e4 := (measurePreserving_mul_left μ h).setIntegral_preimage_emb (measurableEmbedding_mulLeft h)
    (fun g => ⟪π g v, u⟫_ℂ) (h • k)
  rw [e3] at e4
  calc ⟪π h w, u⟫_ℂ = ⟪π h w, π h (π h⁻¹ u)⟫_ℂ := by rw [e1]
    _ = ⟪w, π h⁻¹ u⟫_ℂ := rrc_inner hn h _ _
    _ = ∫ g in k, ⟪π g v, π h⁻¹ u⟫_ℂ ∂μ := hw _
    _ = ∫ g in k, ⟪π (h * g) v, u⟫_ℂ ∂μ := by simp only [e2]
    _ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := e4

omit [LocallyCompactSpace G] [SecondCountableTopology G] [CompleteSpace H] in
theorem rrc_norm_le (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) :
    ‖π h w - w‖ ≤ ‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
  have hkm : MeasurableSet k := hk.measurableSet
  have hk' : IsCompact (h • k) := hk.smul h
  have hkm' : MeasurableSet (h • k) := hk'.measurableSet
  have key : ∀ u, ‖⟪π h w - w, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    intro u
    rw [inner_sub_left, rrc_translate hmul hone hn hw h u, hw u]
    have a1 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm (rrc_intOn hn hm hk'.measure_lt_top v u)
    have a2 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm' (rrc_intOn hn hm hk.measure_lt_top v u)
    rw [inter_comm] at a2
    rw [← a1, ← a2, add_sub_add_left_eq_sub]
    have b1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := h • k \ k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk'.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    have b2 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := k \ h • k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    calc _ ≤ ‖∫ g in h • k \ k, ⟪π g v, u⟫_ℂ ∂μ‖ + ‖∫ g in k \ h • k, ⟪π g v, u⟫_ℂ ∂μ‖ := norm_sub_le _ _
      _ ≤ ‖v‖ * ‖u‖ * μ.real (h • k \ k) + ‖v‖ * ‖u‖ * μ.real (k \ h • k) := add_le_add b1 b2
      _ = _ := by ring
  have h2 := key (π h w - w)
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖((‖π h w - w‖ : ℝ) : ℂ) ^ 2‖ = ‖π h w - w‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, norm_norm]
  have h2' : ‖π h w - w‖ ^ 2 ≤ ‖v‖ * ‖π h w - w‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    rw [← h3]; exact h2
  by_cases h0 : ‖π h w - w‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖π h w - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖π h w - w‖ * ‖π h w - w‖ ≤ ‖π h w - w‖ * (‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k))) := by
      calc _ = ‖π h w - w‖ ^ 2 := by ring
        _ ≤ _ := h2'
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos

theorem rrc_tendsto_vec (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) :
    Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := by
  have t1 : Tendsto (fun h : G => μ (h • k \ k)) (𝓝 1) (𝓝 0) :=
    tendsto_measure_smul_sdiff_isCompact_isClosed hk hk.isClosed
  have t2 : Tendsto (fun h : G => μ (k \ h • k)) (𝓝 1) (𝓝 0) := by
    have e : ∀ h : G, μ (k \ h • k) = μ (h⁻¹ • k \ k) := fun h => by
      rw [← measure_smul μ h⁻¹ (k \ h • k), Set.smul_set_sdiff, inv_smul_smul]
    simp only [e]
    have ti : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact t1.comp ti
  have r1 : Tendsto (fun h : G => μ.real (h • k \ k)) (𝓝 1) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp t1
  have r2 : Tendsto (fun h : G => μ.real (k \ h • k)) (𝓝 1) (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp t2
  have r : Tendsto (fun h : G => ‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k))) (𝓝 1) (𝓝 0) := by
    simpa using (r1.add r2).const_mul ‖v‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => rrc_norm_le hmul hone hn hm hk hw h) r

def rrc_C (π : G → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {x | Tendsto (fun h => π h x) (𝓝 1) (𝓝 x)}
  add_mem' := fun {a b} ha hb => by
    have := Tendsto.add ha hb
    simpa only [mem_ofPred_eq, map_add] using this
  zero_mem' := by
    simp only [mem_ofPred_eq, map_zero]
    exact tendsto_const_nhds
  smul_mem' := fun c a ha => by
    have := Tendsto.const_smul ha c
    simpa only [mem_ofPred_eq, map_smul] using this

theorem rrc_orth [TopologicalSpace.SeparableSpace H] (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1)
    (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) :
    (rrc_C π)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu
  have hz : ∀ v, (fun g => ⟪π g v, u⟫_ℂ) =ᵐ[μ] 0 := by
    intro v
    apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    · rw [locallyIntegrable_iff]
      intro k hk
      exact rrc_intOn hn hm hk.measure_lt_top v u
    · intro k hk
      obtain ⟨w, hw⟩ := rrc_exists_vec hn hm hk.measure_lt_top v
      rw [← hw u]
      exact hu w (rrc_tendsto_vec hmul hone hn hm hk hw)
  have hall : ∀ᵐ g ∂μ, ∀ n, ⟪π g (TopologicalSpace.denseSeq H n), u⟫_ℂ = 0 := ae_all_iff.2 fun n => hz _
  obtain ⟨g, hg⟩ := hall.exists
  have hfun : (fun v => ⟪π g v, u⟫_ℂ) = fun _ => 0 :=
    (TopologicalSpace.denseRange_denseSeq H).equalizer ((π g).continuous.inner continuous_const) continuous_const
      (funext hg)
  have h0 := congrFun hfun (π g⁻¹ u)
  have e1 : π g (π g⁻¹ u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
  simp only [e1] at h0
  exact inner_self_eq_zero.1 h0

theorem rr_cont_of_meas [TopologicalSpace.SeparableSpace H] (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1)
    (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (x : H) :
    Continuous fun g => π g x := by
  have hd : Dense ((rrc_C π : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    exact rrc_orth hmul hone hn hm
  have h1 : ∀ x, Tendsto (fun h => π h x) (𝓝 1) (𝓝 x) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s, hs, hxs⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 3)
    have hs' : Tendsto (fun h => π h s) (𝓝 1) (𝓝 s) := hs
    filter_upwards [(Metric.tendsto_nhds.1 hs') (ε / 3) (by positivity)] with h hh
    have a : dist (π h x) (π h s) = dist x s := by
      rw [dist_eq_norm, ← map_sub, hn, dist_eq_norm]
    calc dist (π h x) x ≤ dist (π h x) (π h s) + dist (π h s) s + dist s x := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [a, dist_comm s x]
          linarith
      _ = ε := by ring
  rw [continuous_iff_continuousAt]
  intro g₀
  have e : (fun g => π g x) = fun g => π g₀ (π (g₀⁻¹ * g) x) := by
    funext g
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel_left]
  have t : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const_mul g₀⁻¹).tendsto g₀
  have c := ((π g₀).continuous.tendsto x).comp ((h1 x).comp t)
  show Tendsto (fun g => π g x) (𝓝 g₀) (𝓝 (π g₀ x))
  rw [e]
  exact c

end Cont

end Formalism.MainNotions.LeviCoordinates

end
