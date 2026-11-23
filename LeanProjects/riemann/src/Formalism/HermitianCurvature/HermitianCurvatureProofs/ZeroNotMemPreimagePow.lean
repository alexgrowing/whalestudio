import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableMainD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermFibreKernels

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def ann (n : ℕ) : Set ℂ := {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}

theorem isCompact_ann (n : ℕ) : IsCompact (ann n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1)).subset fun D hD => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hD.2

theorem zero_notMem_ann (n : ℕ) : (0 : ℂ) ∉ ann n := by
  intro h
  have h1 := h.1
  rw [norm_zero] at h1
  exact absurd h1 (not_le.mpr (by positivity))

theorem ann_mono : Monotone ann := by
  intro m n hmn D hD
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩

theorem exists_mem_ann {D : ℂ} (hD : D ≠ 0) : ∃ n, D ∈ ann n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  refine ⟨n, ?_, ?_⟩
  · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
      (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    exact inv_le_of_inv_le₀ hpos h1
  · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))

theorem isCompact_preimage_pow {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {Q : Set ℂ} (hQ : IsCompact Q) :
    IsCompact {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by
  have hcont : Continuous fun z : ℂ => ε⁻¹ * z ^ s := by fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (hQ.isClosed.preimage hcont) ?_
  obtain ⟨M, hM⟩ := hQ.isBounded.exists_norm_le
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 M)).subset fun z hz => ?_
  have h1 : ‖z‖ ^ s ≤ M := by
    have := hM _ hz
    rwa [norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow] at this
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  have h2 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h3 : ‖z‖ ≤ ‖z‖ ^ s := le_self_pow₀ h2.le hs
  linarith [le_max_right 1 M]

theorem zero_notMem_preimage_pow {s : ℕ} (hs : s ≠ 0) (ε : ℂ) {Q : Set ℂ} (h0 : (0 : ℂ) ∉ Q) :
    (0 : ℂ) ∉ {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by
  intro h
  apply h0
  simpa [zero_pow hs] using h

section ss

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sq_le_eta (a u : H) (η : ℝ) (hη : 0 < η) :
    ‖a‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖u - a‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖u‖ + ‖u - a‖ := by
    calc ‖a‖ = ‖u - (u - a)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - a‖ := norm_sub_le _ _
  have h2 : ‖a‖ ^ 2 ≤ (‖u‖ + ‖u - a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : η * ‖u‖ ^ 2 + η⁻¹ * ‖u - a‖ ^ 2 - 2 * ‖u‖ * ‖u - a‖ = η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by positivity
  nlinarith

theorem stronglyMeasurable_bz (s : ℕ) {bt : ℂ → H} (hbt : StronglyMeasurable bt) :
    StronglyMeasurable (bz s bt) := by
  unfold bz
  have hc : Continuous fun z : ℂ => (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) := by fun_prop
  exact hc.stronglyMeasurable.smul hbt

theorem sq_norm_indicator (Qz : Set ℂ) (f : ℂ → H) :
    (fun z => ‖Qz.indicator f z‖ ^ 2) = Qz.indicator (fun z => ‖f z‖ ^ 2) := by
  funext z
  by_cases hz : z ∈ Qz <;> simp [Set.indicator, hz]

theorem memLp_indicator_bz {s : ℕ} {bt : ℂ → H} (hbt : StronglyMeasurable bt) {Qz : Set ℂ}
    (hQz : MeasurableSet Qz) (hloc : IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) Qz) :
    MemLp (Qz.indicator (bz s bt)) 2 volume := by
  have hm : AEStronglyMeasurable (Qz.indicator (bz s bt)) volume :=
    ((stronglyMeasurable_bz s hbt).indicator hQz).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm, sq_norm_indicator]
  exact (integrable_indicator_iff hQz).2 hloc

theorem integral_bz_Q_le {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt) (Q : Set ℂ)
    (hQ : IsCompact Q) (hloc : IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) {z | ε⁻¹ * z ^ s ∈ Q}) (C : ℝ)
    (hC : ∀ x : ℂ, x ≠ 0 → ∀ᵐ D, D ∈ Q → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    ∫ z, ‖({z | ε⁻¹ * z ^ s ∈ Q}.indicator (bz s bt)) z‖ ^ 2 ≤ SS := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set Qz : Set ℂ := {z | ε⁻¹ * z ^ s ∈ Q} with hQzdef
  have hQzm : MeasurableSet Qz := (isCompact_preimage_pow hs hε hQ).isClosed.measurableSet
  have hbtQ : StronglyMeasurable (Qz.indicator bt) := hbt.indicator hQzm
  have hbQ : MemLp (bz s (Qz.indicator bt)) 2 volume := by
    rw [bz_indicator]; exact memLp_indicator_bz hbt hQzm hloc
  have hSS0 : 0 ≤ SS := le_trans (integral_nonneg fun _ => sq_nonneg _) (sup 1 one_ne_zero)

  have hsh : Tendsto (fun a : ℂ => (s : ℂ) * ((fun _ : ℂ => (1 : ℂ)) a * id a - id a)) (cocompact ℂ) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℂ)) (cocompact ℂ) (𝓝 0))
  have hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 →
      Tendsto (fun a : ℂ => ζ * (fun _ : ℂ => (1 : ℂ)) a * id a - id a) (cocompact ℂ) (cocompact ℂ) := by
    intro ζ _ h1
    refine (tendsto_smul_cocompact (ζ - 1) (sub_ne_zero.2 h1) id tendsto_id).congr fun a => ?_
    simp only [id]
    ring
  have hT := tendsto_pairD hs hβ hε hbQ hbQ id id (fun _ => (1 : ℂ)) 0
    (Eventually.of_forall fun _ => one_ne_zero) tendsto_const_nhds hsh hne
  set L : ℝ := ∫ z, ‖bz s (Qz.indicator bt) z‖ ^ 2 with hL
  have hinner : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := fun v => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hval : ∫ z, G.psi β (0 * z) • ⟪bz s (Qz.indicator bt) z, bz s (Qz.indicator bt) z⟫_ℂ = (L : ℂ) := by
    have hψ0 : ∀ z, G.psi β (0 * z) = 1 := fun z => by simp [G.psi]
    simp_rw [hψ0, one_smul, hinner]
    rw [hL, integral_complex_ofReal]
  rw [hval] at hT

  set f : ℂ → ℝ := fun x => ∫ D, ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2 with hf
  have hpair : ∀ x, pairD s β ε (Qz.indicator bt) (Qz.indicator bt) x x 1 = (f x : ℂ) := by
    intro x
    simp only [pairD, norm_one, one_pow, Complex.ofReal_one, one_smul, one_mul, hinner, hf]
    rw [integral_complex_ofReal]
  have hfT : Tendsto f (cocompact ℂ) (𝓝 L) := by
    have := (Complex.continuous_re.tendsto _).comp hT
    simpa [Function.comp_def, hpair] using this

  have hbound : ∀ η : ℝ, 0 < η → L ≤ (1 + η) * SS := by
    intro η hη
    obtain ⟨vQ, hvQ⟩ : ∃ v : ℝ, v = (volume Q).toReal := ⟨_, rfl⟩
    have hg : Tendsto (fun x : ℂ => (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ) (cocompact ℂ)
        (𝓝 ((1 + η) * SS)) := by
      have h0 : Tendsto (fun x : ℂ => ‖x‖⁻¹) (cocompact ℂ) (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
      have h1 : Tendsto (fun x : ℂ => (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ) (cocompact ℂ)
          (𝓝 ((1 + η) * SS + (1 + η⁻¹) * (C * 0) ^ 2 * vQ)) :=
        tendsto_const_nhds.add ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul h0).pow 2)).mul tendsto_const_nhds)
      simpa using h1
    refine le_of_tendsto_of_tendsto hfT hg ?_
    filter_upwards [eventually_ne_cocompact 0] with x hx
    have hmD : MemLp (mainD s β ε (Qz.indicator bt) x) 2 volume := memLp_mainD hs β hε hbtQ hbQ x
    have i1 : Integrable (fun D => ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmD.1).1 hmD
    have i2 : Integrable (fun D => ‖ut x D‖ ^ 2) := (memLp_two_iff_integrable_sq_norm (memU x hx).1).1 (memU x hx)
    have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
    have i3 : Integrable (Q.indicator fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) :=
      (integrableOn_const hQ.measure_lt_top.ne).integrable_indicator hQm
    have hpt : ∀ᵐ D, ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2 ≤
        (1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D := by
      filter_upwards [hC x hx] with D hD
      rw [mainD_indicator hs β hε0 bt Q x D]
      by_cases hDQ : D ∈ Q
      · rw [Set.indicator_of_mem hDQ, Set.indicator_of_mem hDQ]
        have hr := hD hDQ
        have hr2 : ‖ut x D - mainD s β ε bt x D‖ ^ 2 ≤ (C * ‖x‖⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hr 2
        have := norm_sq_le_eta (mainD s β ε bt x D) (ut x D) η hη
        have hc : 0 ≤ 1 + η⁻¹ := by positivity
        nlinarith
      · rw [Set.indicator_of_notMem hDQ, Set.indicator_of_notMem hDQ, norm_zero]
        have : 0 ≤ (1 + η) * ‖ut x D‖ ^ 2 := by positivity
        simpa using this
    calc f x ≤ ∫ D, ((1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D) :=
          integral_mono_ae i1 ((i2.const_mul _).add i3) hpt
      _ = (1 + η) * (∫ D, ‖ut x D‖ ^ 2) + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
          have e1 : ∫ D, ((1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D) =
              (1 + η) * (∫ D, ‖ut x D‖ ^ 2) + ∫ D, Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D := by
            rw [integral_add (i2.const_mul _) i3, integral_const_mul]
          have e2 : ∫ D, Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D =
              (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
            rw [integral_indicator hQm, setIntegral_const, smul_eq_mul, hvQ, Measure.real, mul_comm]
          rw [e1, e2]
      _ ≤ (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
          have := mul_le_mul_of_nonneg_left (sup x hx) (by positivity : (0 : ℝ) ≤ 1 + η)
          linarith

  rw [← bz_indicator]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hη : 0 < δ / (SS + 1) := by positivity
  have h1 := hbound _ hη
  have h2 : (1 + δ / (SS + 1)) * SS < SS + δ := by
    have : δ / (SS + 1) * SS < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

end ss

end

end Formalism.FourierDecayAlt.P.PBK
