import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace

theorem rrd_countable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  have hsep : ∀ i j, i ≠ j → 1 ≤ ‖v i - v j‖ := by
    intro i j hij
    have h2 : ‖v i - v j‖ ^ 2 = 2 := by
      first
      | rw [norm_sub_sq (𝕜 := ℂ), hv.1 i, hv.1 j, hv.2 hij]; norm_num
      | rw [@norm_sub_sq ℂ, hv.1 i, hv.1 j, hv.2 hij]; norm_num
    nlinarith [norm_nonneg (v i - v j)]
  have hdisj : (Set.univ : Set ι).PairwiseDisjoint (fun i => Metric.ball (v i) (1 / 2 : ℝ)) := by
    intro i _ j _ hij
    show Disjoint (Metric.ball (v i) (1 / 2 : ℝ)) (Metric.ball (v j) (1 / 2 : ℝ))
    refine Set.disjoint_left.2 fun w hwi hwj => ?_
    have h1 := hsep i j hij
    rw [Metric.mem_ball] at hwi hwj
    have h3 : dist (v i) (v j) < 1 := by
      calc dist (v i) (v j) ≤ dist (v i) w + dist w (v j) := dist_triangle _ _ _
        _ = dist w (v i) + dist w (v j) := by rw [dist_comm (v i) w]
        _ < 1 / 2 + 1 / 2 := add_lt_add hwi hwj
        _ = 1 := by norm_num
    rw [dist_eq_norm] at h3
    linarith
  have hc := hdisj.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
    (fun i _ => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.1 hc

theorem rrd_stronglyMeasurable {α : Type*} [MeasurableSpace α] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H] (F : α → H)
    (hF : ∀ x, StronglyMeasurable fun a => ⟪x, F a⟫_ℂ) : StronglyMeasurable F := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  haveI : Countable w := rrd_countable b.orthonormal
  haveI : Encodable w := Encodable.ofCountable w
  have hterm : ∀ i : w, StronglyMeasurable fun a => ⟪b i, F a⟫_ℂ • b i := by
    intro i
    first
    | exact (hF (b i)).smul_const (b i)
    | exact (hF (b i)).smul stronglyMeasurable_const
  have hfin : ∀ s : Finset w, StronglyMeasurable fun a => ∑ i ∈ s, ⟪b i, F a⟫_ℂ • b i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact stronglyMeasurable_const
    · intro i t hi ih
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hlim : Tendsto (fun (s : Finset w) (a : α) => ∑ i ∈ s, ⟪b i, F a⟫_ℂ • b i) atTop (𝓝 F) := by
    rw [tendsto_pi_nhds]
    intro a
    have h := b.hasSum_repr (F a)
    simp only [HilbertBasis.repr_apply_apply] at h
    exact h
  first
  | exact stronglyMeasurable_of_tendsto atTop hfin hlim
  | exact StronglyMeasurable.of_tendsto atTop hfin hlim

section Trans

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]

private theorem integrable_comp_mul_left' {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] {f : G → E} (hf : Integrable f μ) (h : G) :
    Integrable (fun g => f (h * g)) μ := by
  first
  | exact hf.comp_mul_left h
  | exact hf.comp_mul_left' h

private theorem integral_comp_mul_left_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G → E) (h : G) :
    ∫ g, f (h * g) ∂μ = ∫ g, f g ∂μ := by
  first
  | exact integral_mul_left_eq_self f h
  | exact integral_comp_mul_left f h

private theorem abs_norm_sub_sub_norm_add_norm_le_two_mul (a b : ℂ) : |‖a - b‖ - ‖a‖ + ‖b‖| ≤ 2 * ‖b‖ := by
  have h1 := norm_sub_le a b
  have h2 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  rw [abs_le]
  constructor <;> linarith [norm_nonneg b, norm_nonneg a, norm_nonneg (a - b)]

theorem rrd_translate (f : G → ℂ) (hc : Continuous f) (hf : Integrable f μ) :
    Tendsto (fun h : G => ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have key : ∀ h : G, ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ =
      ∫ g, (‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) ∂μ := by
    intro h
    have i1 : Integrable (fun g => f (h⁻¹ * g)) μ := integrable_comp_mul_left' hf h⁻¹
    have i2 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖) μ := (i1.sub hf).norm
    have e : ∫ g, ‖f (h⁻¹ * g)‖ ∂μ = ∫ g, ‖f g‖ ∂μ := integral_comp_mul_left_eq (fun g => ‖f g‖) h⁻¹
    have i3 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖) μ := i2.sub i1.norm
    rw [integral_add i3 hf.norm, integral_sub i2 i1.norm, e]
    ring
  have hfun : (fun h : G => ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ) =
      fun h => ∫ g, (‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) ∂μ := funext key
  rw [hfun]
  have hmeas : ∀ᶠ h in 𝓝 (1 : G),
      AEStronglyMeasurable (fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) μ :=
    Filter.Eventually.of_forall fun h =>
      (by fun_prop : Continuous fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖).aestronglyMeasurable
  have hbound : ∀ᶠ h in 𝓝 (1 : G), ∀ᵐ g ∂μ, ‖‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖‖ ≤ 2 * ‖f g‖ :=
    Filter.Eventually.of_forall fun h => Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      exact abs_norm_sub_sub_norm_add_norm_le_two_mul _ _
  have hlim : ∀ᵐ g ∂μ, Tendsto (fun h : G => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) (𝓝 1) (𝓝 0) :=
    Filter.Eventually.of_forall fun g => by
      have hcont : Continuous fun h : G => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖ := by fun_prop
      simpa using hcont.tendsto 1
  have := tendsto_integral_filter_of_dominated_convergence (fun g => 2 * ‖f g‖) hmeas hbound
    (hf.norm.const_mul 2) hlim
  simpa using this

private theorem integrable_mul_of_norm_le_of_stronglyMeasurable {α : Type*} [MeasurableSpace α] {ν : Measure α} {f ψ : α → ℂ}
    (hf : Integrable f ν) (hψ : StronglyMeasurable ψ) (M : ℝ) (hM : ∀ g, ‖ψ g‖ ≤ M) :
    Integrable (fun g => f g * ψ g) ν := by
  refine Integrable.mono' (hf.norm.mul_const M) (hf.aestronglyMeasurable.mul hψ.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM g) (norm_nonneg _)

theorem rrd_ae_zero [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (ψ : G → ℂ) (hψ : StronglyMeasurable ψ) (M : ℝ)
    (hM : ∀ g, ‖ψ g‖ ≤ M) (h0 : ∀ f : G → ℂ, Continuous f → Integrable f μ → ∫ g, f g * ψ g ∂μ = 0) :
    ψ =ᵐ[μ] 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hreg : μ.WeaklyRegular := by
    first
    | infer_instance
    | exact Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
  have hint_r : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn ψ s μ := by
    intro s hs hμs
    have hc : IntegrableOn (fun _ : G => M) s μ := by
      first
      | exact integrableOn_const hμs.ne
      | exact integrableOn_const.2 (Or.inr hμs)
      | exact integrableOn_const_iff.2 (Or.inr hμs)
    exact Integrable.mono' hc hψ.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  have hzero : ∀ s, MeasurableSet s → μ s < ⊤ → ∫ x in s, ψ x ∂μ = 0 := by
    intro s hs hμs
    have hk : Integrable (s.indicator fun _ : G => (1 : ℂ)) μ := by
      rw [integrable_indicator_iff hs]
      first
      | exact integrableOn_const hμs.ne
      | exact integrableOn_const.2 (Or.inr hμs)
      | exact integrableOn_const_iff.2 (Or.inr hμs)
    have hI : ∫ x in s, ψ x ∂μ = ∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ := by
      rw [← integral_indicator hs]
      congr 1
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hI]
    have key : ∀ ε > 0, ‖∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ‖ ≤ ε := by
      intro ε hε
      have hε' : 0 < ε / (M + 1) := div_pos hε hM1
      obtain ⟨φ, hφ⟩ := hk.exists_boundedContinuous_integral_sub_le hε'
      have hφi : Integrable (⇑φ) μ := by
        first
        | exact hφ.2
        | exact hφ.1
      have hφd : ∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ ∂μ ≤ ε / (M + 1) := by
        first
        | exact hφ.1
        | exact hφ.2
      have e : ∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ =
          ∫ x, (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x ∂μ := by
        have hsplit : (fun x => (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x) =
            fun x => s.indicator (fun _ : G => (1 : ℂ)) x * ψ x - φ x * ψ x :=
          funext fun x => sub_mul _ _ _
        rw [hsplit, integral_sub (integrable_mul_of_norm_le_of_stronglyMeasurable hk hψ M hM) (integrable_mul_of_norm_le_of_stronglyMeasurable hφi hψ M hM),
          h0 φ φ.continuous hφi, sub_zero]
      rw [e]
      calc ‖∫ x, (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x ∂μ‖
          ≤ ∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ * M ∂μ := by
            refine norm_integral_le_of_norm_le ((hk.sub hφi).norm.mul_const M)
              (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
        _ = (∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ ∂μ) * M := integral_mul_const _ _
        _ ≤ ε / (M + 1) * M := mul_le_mul_of_nonneg_right hφd hM0
        _ ≤ ε / (M + 1) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
        _ = ε := by field_simp
    by_contra hne
    have hpos : 0 < ‖∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ‖ := norm_pos_iff.2 hne
    have := key _ (half_pos hpos)
    linarith
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint_r hzero

end Trans

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}

def rrd_vec (μ : Measure G) (π : G → (H →L[ℂ] H)) (f : G → ℂ) (v : H) : H := ∫ g, f g • π g v ∂μ

theorem rrd_int (hiso : ∀ g x, ‖π g x‖ = ‖x‖) (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ)
    {f : G → ℂ} (hf : Integrable f μ) (v : H) : Integrable (fun g => f g • π g v) μ := by
  have hm : StronglyMeasurable fun g => π g v := rrd_stronglyMeasurable _ fun x => hmeas x v
  refine Integrable.mono' (hf.norm.mul_const ‖v‖) (hf.aestronglyMeasurable.smul hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  exact le_of_eq (by rw [norm_smul, hiso])

theorem rrd_act (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) {f : G → ℂ} (hf : Integrable f μ) (v : H) (h : G) :
    π h (rrd_vec μ π f v) = ∫ g, f (h⁻¹ * g) • π g v ∂μ := by
  unfold rrd_vec
  rw [← ContinuousLinearMap.integral_comp_comm (π h) (rrd_int hiso hmeas hf v)]
  calc ∫ g, π h (f g • π g v) ∂μ = ∫ g, f (h⁻¹ * (h * g)) • π (h * g) v ∂μ := by
        congr 1
        funext g
        rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.comp_apply, map_smul]
    _ = ∫ g, f (h⁻¹ * g) • π g v ∂μ := integral_comp_mul_left_eq (fun g => f (h⁻¹ * g) • π g v) h

theorem rrd_vec_tendsto (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) {f : G → ℂ} (hc : Continuous f) (hf : Integrable f μ)
    (v : H) : Tendsto (fun h => π h (rrd_vec μ π f v)) (𝓝 1) (𝓝 (rrd_vec μ π f v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hT := (rrd_translate (μ := μ) f hc hf).mul_const ‖v‖
  rw [zero_mul] at hT
  refine squeeze_zero (fun h => norm_nonneg _) (fun h => ?_) hT
  rw [rrd_act hmul hiso hmeas hf v h]
  have i1 : Integrable (fun g => f (h⁻¹ * g) • π g v) μ :=
    rrd_int hiso hmeas (integrable_comp_mul_left' hf h⁻¹) v
  have i2 : Integrable (fun g => f g • π g v) μ := rrd_int hiso hmeas hf v
  have i3 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖ * ‖v‖) μ :=
    ((integrable_comp_mul_left' hf h⁻¹).sub hf).norm.mul_const _
  unfold rrd_vec
  rw [← integral_sub i1 i2, ← integral_mul_const]
  refine norm_integral_le_of_norm_le i3 (Filter.Eventually.of_forall fun g => le_of_eq ?_)
  rw [← sub_smul, norm_smul, hiso]

theorem rrd_inner_vec (hiso : ∀ g x, ‖π g x‖ = ‖x‖) (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ)
    {f : G → ℂ} (hf : Integrable f μ) (u v : H) : ⟪u, rrd_vec μ π f v⟫_ℂ = ∫ g, f g * ⟪u, π g v⟫_ℂ ∂μ := by
  unfold rrd_vec
  rw [← integral_inner (rrd_int hiso hmeas hf v) u]
  congr 1
  funext g
  rw [inner_smul_right]

theorem rr_cont_of_meas' [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) (x : H) : Continuous fun g => π g x := by
  let W : Submodule ℂ H :=
    { carrier := {w | Tendsto (fun h => π h w) (𝓝 1) (𝓝 w)}
      add_mem' := fun {a b} ha hb => by
        have ha' : Tendsto (fun h => π h a) (𝓝 1) (𝓝 a) := ha
        have hb' : Tendsto (fun h => π h b) (𝓝 1) (𝓝 b) := hb
        exact (ha'.add hb').congr fun h => (map_add (π h) a b).symm
      zero_mem' := by
        show Tendsto (fun h => π h 0) (𝓝 1) (𝓝 0)
        simp only [map_zero]
        exact tendsto_const_nhds
      smul_mem' := fun c {w} hw => by
        have hw' : Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := hw
        exact (hw'.const_smul c).congr fun h => (map_smul (π h) c w).symm }
  have memW : ∀ w, w ∈ W ↔ Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := fun w => Iff.rfl
  have hclosed : IsClosed (W : Set H) := by
    refine isClosed_of_closure_subset fun w hw => ?_
    rw [SetLike.mem_coe, memW, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨w', hw', hd⟩ := Metric.mem_closure_iff.1 hw (ε / 3) (by positivity)
    rw [SetLike.mem_coe, memW, Metric.tendsto_nhds] at hw'
    filter_upwards [hw' (ε / 3) (by positivity)] with h hh
    have e1 : dist (π h w) (π h w') = dist w w' := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hiso]
    calc dist (π h w) w ≤ dist (π h w) (π h w') + dist (π h w') w' + dist w' w := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [e1, dist_comm w' w]; linarith
      _ = ε := by ring
  have hperp : W.orthogonal = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hae : ∀ v : H, ∀ᵐ g ∂μ, ⟪u, π g v⟫_ℂ = 0 := by
      intro v
      have hz := rrd_ae_zero (μ := μ) (fun g => ⟪u, π g v⟫_ℂ) (hmeas u v)
        (‖u‖ * ‖v‖) (fun g => ?_) (fun f hc hf => ?_)
      · filter_upwards [hz] with g hg
        simpa using hg
      · calc ‖⟪u, π g v⟫_ℂ‖ ≤ ‖u‖ * ‖π g v‖ := norm_inner_le_norm _ _
          _ = ‖u‖ * ‖v‖ := by rw [hiso]
      · show ∫ g, f g * ⟪u, π g v⟫_ℂ ∂μ = 0
        rw [← rrd_inner_vec hiso hmeas hf u v]
        have hw : rrd_vec μ π f v ∈ W :=
          (memW _).2 (rrd_vec_tendsto hmul hiso hmeas hc hf v)
        first
        | exact Submodule.inner_left_of_mem_orthogonal hw hu
        | exact (Submodule.mem_orthogonal' W u).1 hu _ hw
        | exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal W u).1 hu _ hw)
    have hall : ∀ᵐ g ∂μ, ∀ n : ℕ, ⟪u, π g (denseSeq H n)⟫_ℂ = 0 := ae_all_iff.2 fun n => hae _
    haveI : (ae μ).NeBot := ae_neBot.2 hμ
    obtain ⟨g, hg⟩ := hall.exists
    have hzero : ∀ y : H, ⟪u, π g y⟫_ℂ = 0 := fun y =>
      (denseRange_denseSeq H).induction_on y
        (isClosed_eq (continuous_const.inner (π g).continuous) continuous_const) hg
    have e : π g ∘L π g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have e2 : π g (π g⁻¹ u) = u := by
      have := congrArg (fun T : H →L[ℂ] H => T u) e
      simpa using this
    have hu' : ⟪u, u⟫_ℂ = 0 := by
      have := hzero (π g⁻¹ u)
      rwa [e2] at this
    exact inner_self_eq_zero.1 hu'
  have htc : W.topologicalClosure = ⊤ := by
    first
    | exact Submodule.topologicalClosure_eq_top_iff.2 hperp
    | exact (Submodule.topologicalClosure_eq_top_iff W).2 hperp
  have hx : ∀ x : H, Tendsto (fun h => π h x) (𝓝 1) (𝓝 x) := by
    intro x
    have h1 : x ∈ W.topologicalClosure := by
      rw [htc]
      exact Submodule.mem_top
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, hclosed.closure_eq, SetLike.mem_coe] at h1
    exact (memW x).1 h1
  refine continuous_iff_continuousAt.2 fun g0 => ?_
  have t1 : Tendsto (fun g => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
    simpa using (continuous_mul_left g0⁻¹).tendsto g0
  have t2 := ((π g0).continuous.tendsto x).comp ((hx x).comp t1)
  refine t2.congr fun g => ?_
  have e : π g = π g0 ∘L π (g0⁻¹ * g) := by rw [← hmul, mul_inv_cancel_left]
  simp only [Function.comp_apply, e, ContinuousLinearMap.comp_apply]

end Main

end Formalism.MainNotions.LeviCoordinates

end
