import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.GraphTrick

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def graph (μ : Measure G) (ρ : G → (H →L[ℂ] H)) (w₀ : H) : Submodule ℂ (WithLp 2 (H × Lp ℂ 2 μ)) where
  carrier := {p | (p.snd : G → ℂ) =ᵐ[μ] fun g => ⟪w₀, ρ g p.fst⟫_ℂ}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq, WithLp.add_fst, WithLp.add_snd] at *
    filter_upwards [Lp.coeFn_add p.snd q.snd, hp, hq] with g h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, map_add, inner_add_right]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, WithLp.zero_fst, WithLp.zero_snd, map_zero, inner_zero_right]
    exact Lp.coeFn_zero _ _ _
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_ofPred_eq, WithLp.smul_fst, WithLp.smul_snd] at *
    filter_upwards [Lp.coeFn_smul c p.snd, hp] with g h1 h2
    rw [h1, Pi.smul_apply, h2, map_smul, inner_smul_right, smul_eq_mul]

theorem graph_isClosed (ρ : G → (H →L[ℂ] H)) (w₀ : H) : IsClosed (graph μ ρ w₀ : Set (WithLp 2 (H × Lp ℂ 2 μ))) := by
  refine IsSeqClosed.isClosed (fun {u} {p} hu hlim => ?_)
  have h1 : Tendsto (fun n => (u n).fst) atTop (𝓝 p.fst) :=
    ((WithLp.fstL 2 ℂ H (Lp ℂ 2 μ)).continuous.tendsto p).comp hlim
  have h2 : Tendsto (fun n => (u n).snd) atTop (𝓝 p.snd) :=
    ((WithLp.sndL 2 ℂ H (Lp ℂ 2 μ)).continuous.tendsto p).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ k, ((u k).snd : G → ℂ) g = ⟪w₀, ρ g (u k).fst⟫_ℂ := ae_all_iff.mpr (fun k => hu k)
  show ((p.snd : G → ℂ)) =ᵐ[μ] fun g => ⟪w₀, ρ g p.fst⟫_ℂ
  filter_upwards [hae, hall] with g hg1 hg2
  have h3 : Tendsto (fun i => ((u (ns i)).snd : G → ℂ) g) atTop (𝓝 ⟪w₀, ρ g p.fst⟫_ℂ) := by
    simp_rw [hg2]
    have h4 : Tendsto (fun i => (u (ns i)).fst) atTop (𝓝 p.fst) := h1.comp hns.tendsto_atTop
    exact (((innerSL ℂ w₀).comp (ρ g)).continuous.tendsto p.fst).comp h4
  exact tendsto_nhds_unique hg1 h3

section Rep

variable (ρ : G → (H →L[ℂ] H)) (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)

def rt (h : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ (fun g => g * h) (hR h)

theorem rt_ae (h : G) (f : Lp ℂ 2 μ) : (rt hR h f : G → ℂ) =ᵐ[μ] fun g => f (g * h) := by
  first
  | exact Lp.coeFn_compMeasurePreserving f (hR h)
  | (unfold rt; exact Lp.coeFn_compMeasurePreserving f (hR h))

theorem rt_rt_inv (h : G) (f : Lp ℂ 2 μ) : rt hR h (rt hR h⁻¹ f) = f := by
  apply Lp.ext
  refine (rt_ae hR h (rt hR h⁻¹ f)).trans
    (((hR h).quasiMeasurePreserving.ae_eq_comp (rt_ae hR h⁻¹ f)).trans (ae_of_all _ (fun g => ?_)))
  show f (g * h * h⁻¹) = f g
  rw [mul_inv_cancel_right]

def act (h : G) (p : WithLp 2 (H × Lp ℂ 2 μ)) : WithLp 2 (H × Lp ℂ 2 μ) :=
  WithLp.toLp 2 (ρ h p.fst, rt hR h p.snd)

variable {ρ}

theorem act_inner (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖) (h : G) (p q : WithLp 2 (H × Lp ℂ 2 μ)) :
    ⟪act ρ hR h p, act ρ hR h q⟫_ℂ = ⟪p, q⟫_ℂ := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  show ⟪ρ h p.fst, ρ h q.fst⟫_ℂ + ⟪rt hR h p.snd, rt hR h q.snd⟫_ℂ = ⟪p.fst, q.fst⟫_ℂ + ⟪p.snd, q.snd⟫_ℂ
  have e1 : ⟪ρ h p.fst, ρ h q.fst⟫_ℂ = ⟪p.fst, q.fst⟫_ℂ :=
    ({ toLinearMap := (ρ h : H →ₗ[ℂ] H), norm_map' := hiso h } : H →ₗᵢ[ℂ] H).inner_map_map p.fst q.fst
  rw [e1, (rt hR h).inner_map_map p.snd q.snd]

theorem act_act_inv (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (h : G)
    (p : WithLp 2 (H × Lp ℂ 2 μ)) : act ρ hR h (act ρ hR h⁻¹ p) = p := by
  have e1 : ρ h (ρ h⁻¹ p.fst) = p.fst := by
    have := congrArg (fun T : H →L[ℂ] H => T p.fst) (hmul h h⁻¹)
    simp only [mul_inv_cancel, hone, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at this
    exact this.symm
  show WithLp.toLp 2 (ρ h (ρ h⁻¹ p.fst), rt hR h (rt hR h⁻¹ p.snd)) = p
  rw [e1, rt_rt_inv]
  rfl

theorem act_mem (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (w₀ : H) (h : G) {p : WithLp 2 (H × Lp ℂ 2 μ)}
    (hp : p ∈ graph μ ρ w₀) : act ρ hR h p ∈ graph μ ρ w₀ := by
  have hp' : ((p.snd : G → ℂ)) =ᵐ[μ] fun g => ⟪w₀, ρ g p.fst⟫_ℂ := hp
  show ((rt hR h p.snd : G → ℂ)) =ᵐ[μ] fun g => ⟪w₀, ρ g (ρ h p.fst)⟫_ℂ
  refine (rt_ae hR h p.snd).trans
    (((hR h).quasiMeasurePreserving.ae_eq_comp hp').trans (ae_of_all _ (fun g => ?_)))
  show ⟪w₀, ρ (g * h) p.fst⟫_ℂ = ⟪w₀, ρ g (ρ h p.fst)⟫_ℂ
  rw [hmul]
  rfl

end Rep

section Main

variable {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)

theorem proj_act (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (w₀ : H) [(graph μ ρ w₀).HasOrthogonalProjection] (h : G) (y : WithLp 2 (H × Lp ℂ 2 μ)) :
    (graph μ ρ w₀).starProjection (act ρ hR h y) = act ρ hR h ((graph μ ρ w₀).starProjection y) := by
  have hmemP : ∀ z, (graph μ ρ w₀).starProjection z ∈ graph μ ρ w₀ := by
    intro z
    first
    | exact Submodule.starProjection_apply_mem _ z
    | (rw [Submodule.starProjection_apply]; exact ((graph μ ρ w₀).orthogonalProjection z).2)
  have horth : ∀ z, z - (graph μ ρ w₀).starProjection z ∈ (graph μ ρ w₀)ᗮ := by
    intro z
    first
    | exact Submodule.sub_starProjection_mem_orthogonal z
    | exact (graph μ ρ w₀).sub_starProjection_mem_orthogonal z
    | (rw [Submodule.starProjection_apply]; exact Submodule.sub_orthogonalProjection_mem_orthogonal z)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (act_mem hR hmul w₀ h (hmemP y))
  intro z hz
  rw [← act_act_inv hR hone hmul h z, inner_sub_left, act_inner hR hiso, act_inner hR hiso,
    ← inner_sub_left]
  exact Submodule.inner_left_of_mem_orthogonal (act_mem hR hmul w₀ h⁻¹ hz) (horth y)

def bop (Γ : Submodule ℂ (WithLp 2 (H × Lp ℂ 2 μ))) [Γ.HasOrthogonalProjection] : H →L[ℂ] H :=
  WithLp.fstL 2 ℂ H (Lp ℂ 2 μ) ∘L Γ.starProjection ∘L
    ((WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp ℂ 2 μ)).symm : H × Lp ℂ 2 μ →L[ℂ] WithLp 2 (H × Lp ℂ 2 μ)) ∘L
      ContinuousLinearMap.inl ℂ H (Lp ℂ 2 μ)

theorem bop_apply (Γ : Submodule ℂ (WithLp 2 (H × Lp ℂ 2 μ))) [Γ.HasOrthogonalProjection] (x : H) :
    bop Γ x = (Γ.starProjection (WithLp.toLp 2 (x, (0 : Lp ℂ 2 μ)))).fst := rfl

theorem star_eq (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (h : G) : star (ρ h) = ρ h⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hinv : ρ h (ρ h⁻¹ x) = x := by
    have := congrArg (fun T : H →L[ℂ] H => T x) (hmul h h⁻¹)
    simp only [mul_inv_cancel, hone, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at this
    exact this.symm
  have hI : ⟪ρ h (ρ h⁻¹ x), ρ h y⟫_ℂ = ⟪ρ h⁻¹ x, y⟫_ℂ :=
    ({ toLinearMap := (ρ h : H →ₗ[ℂ] H), norm_map' := hiso h } : H →ₗᵢ[ℂ] H).inner_map_map _ _
  rw [← hI, hinv]

include hR in

theorem memLp_of_ne (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (w₀ x₀ : H) (hx₀ : x₀ ≠ 0) (h0 : MemLp (fun g => ⟪w₀, ρ g x₀⟫_ℂ) 2 μ) (x : H) :
    MemLp (fun g => ⟪w₀, ρ g x⟫_ℂ) 2 μ := by
  have schur : ∀ B : H →L[ℂ] H, IsSelfAdjoint B → (∀ g, Commute B (ρ g)) →
      ∃ c : ℝ, B = algebraMap ℝ (H →L[ℂ] H) c := by
    intro B hB hc
    have hker : ∀ X : H →L[ℂ] H, (∀ g, Commute X (ρ g)) → X = 0 ∨ Function.Injective X := by
      intro X hX
      have hinv : ∀ g, ∀ v ∈ LinearMap.ker (X : H →ₗ[ℂ] H), ρ g v ∈ LinearMap.ker (X : H →ₗ[ℂ] H) := by
        intro g v hv
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
        have := congrArg (fun Y : H →L[ℂ] H => Y v) (hX g).eq
        simp only [ContinuousLinearMap.mul_apply, hv, map_zero] at this
        exact this
      rcases hirr (LinearMap.ker (X : H →ₗ[ℂ] H)) X.isClosed_ker hinv with h | h
      · right
        intro a b hab
        have hm : a - b ∈ LinearMap.ker (X : H →ₗ[ℂ] H) := by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hab, sub_self]
        rw [h] at hm
        exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hm)
      · left
        ext v
        have hv : v ∈ LinearMap.ker (X : H →ₗ[ℂ] H) := by rw [h]; trivial
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
        rw [hv, ContinuousLinearMap.zero_apply]
    have hcf : ∀ f : ℝ → ℝ, ∀ g, Commute (cfc f B) (ρ g) := by
      intro f g
      first
      | exact (hc g).cfc_real f
      | exact hB.commute_cfc (hc g) f
      | exact Commute.cfc_real (hc g) f
      | exact (hc g).cfc (by rw [hB.star_eq]; exact hc g) f
    have hsub : ∀ a ∈ spectrum ℝ B, ∀ b ∈ spectrum ℝ B, a = b := by
      intro a ha b hb
      by_contra hab
      wlog hlt : a < b generalizing a b
      · exact this b hb a ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
      obtain ⟨m, hm1, hm2⟩ : ∃ m : ℝ, a < m ∧ m < b := ⟨(a + b) / 2, by linarith, by linarith⟩
      have hf : Continuous (fun x : ℝ => max (x - m) 0) := (continuous_id.sub continuous_const).max continuous_const
      have hg : Continuous (fun x : ℝ => max (m - x) 0) := (continuous_const.sub continuous_id).max continuous_const
      have hfne : cfc (fun x : ℝ => max (x - m) 0) B ≠ 0 := by
        intro h0
        have h1 : max (b - m) 0 = 0 := by
          first
          | exact (eqOn_of_cfc_eq_cfc (h0.trans (cfc_zero ℝ B).symm) (hf := hf.continuousOn) (hg := continuousOn_const) (ha := hB)) hb
          | exact (eqOn_of_cfc_eq_cfc (h0.trans (cfc_const_zero ℝ B).symm) (hf := hf.continuousOn) (hg := continuousOn_const) (ha := hB)) hb
          | exact eqOn_of_cfc_eq_cfc (h0.trans (cfc_zero (R := ℝ) B).symm) (hf := hf.continuousOn) (ha := hB) hb
          | exact eqOn_of_cfc_eq_cfc (h0.trans (cfc_const_zero (R := ℝ) B).symm) (hf := hf.continuousOn) (ha := hB) hb
        have h2 : b - m ≤ 0 := by rw [← h1]; exact le_max_left _ _
        linarith
      have hgne : cfc (fun x : ℝ => max (m - x) 0) B ≠ 0 := by
        intro h0
        have h1 : max (m - a) 0 = 0 := by
          first
          | exact (eqOn_of_cfc_eq_cfc (h0.trans (cfc_zero ℝ B).symm) (hf := hg.continuousOn) (hg := continuousOn_const) (ha := hB)) ha
          | exact (eqOn_of_cfc_eq_cfc (h0.trans (cfc_const_zero ℝ B).symm) (hf := hg.continuousOn) (hg := continuousOn_const) (ha := hB)) ha
          | exact eqOn_of_cfc_eq_cfc (h0.trans (cfc_zero (R := ℝ) B).symm) (hf := hg.continuousOn) (ha := hB) ha
          | exact eqOn_of_cfc_eq_cfc (h0.trans (cfc_const_zero (R := ℝ) B).symm) (hf := hg.continuousOn) (ha := hB) ha
        have h2 : m - a ≤ 0 := by rw [← h1]; exact le_max_left _ _
        linarith
      have hfg : cfc (fun x : ℝ => max (x - m) 0) B * cfc (fun x : ℝ => max (m - x) 0) B = 0 := by
        rw [← cfc_mul (fun x : ℝ => max (x - m) 0) (fun x : ℝ => max (m - x) 0) B
          (hf := hf.continuousOn) (hg := hg.continuousOn)]
        have h3 : (fun x : ℝ => max (x - m) 0 * max (m - x) 0) = fun _ => (0 : ℝ) := by
          funext x
          rcases le_total x m with h | h
          · rw [max_eq_right (by linarith : x - m ≤ 0), zero_mul]
          · rw [max_eq_right (by linarith : m - x ≤ 0), mul_zero]
        rw [h3]
        first
        | exact cfc_const_zero ℝ B
        | exact cfc_zero ℝ B
        | simp
      rcases hker _ (hcf (fun x : ℝ => max (x - m) 0)) with h1 | h1
      · exact hfne h1
      · apply hgne
        ext v
        apply h1
        simp only [ContinuousLinearMap.zero_apply, map_zero]
        rw [← ContinuousLinearMap.mul_apply, hfg, ContinuousLinearMap.zero_apply]
    by_cases hne : (spectrum ℝ B).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, ?_⟩
      calc B = cfc (id : ℝ → ℝ) B := (cfc_id ℝ B hB).symm
        _ = cfc (fun _ : ℝ => c) B := cfc_congr (fun x hx => hsub x hx c hc')
        _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c B hB
    · refine ⟨0, ?_⟩
      calc B = cfc (id : ℝ → ℝ) B := (cfc_id ℝ B hB).symm
        _ = cfc (fun _ : ℝ => (0 : ℝ)) B := cfc_congr (fun x hx => absurd ⟨x, hx⟩ hne)
        _ = algebraMap ℝ (H →L[ℂ] H) 0 := cfc_const 0 B hB
  haveI : CompleteSpace (graph μ ρ w₀) := (graph_isClosed ρ w₀).completeSpace_coe
  have hmemP : ∀ z, (graph μ ρ w₀).starProjection z ∈ graph μ ρ w₀ := by
    intro z
    first
    | exact Submodule.starProjection_apply_mem _ z
    | (rw [Submodule.starProjection_apply]; exact ((graph μ ρ w₀).orthogonalProjection z).2)
  have hsa : ∀ u v : WithLp 2 (H × Lp ℂ 2 μ),
      ⟪(graph μ ρ w₀).starProjection u, v⟫_ℂ = ⟪u, (graph μ ρ w₀).starProjection v⟫_ℂ := by
    intro u v
    first
    | exact Submodule.inner_starProjection_left_eq_right _ u v
    | exact Submodule.inner_starProjection_left_eq_right u v
    | (simp only [Submodule.starProjection_apply]; exact inner_orthogonalProjection_left_eq_right _ u v)
  have hsym : ∀ x y : H, ⟪bop (graph μ ρ w₀) x, y⟫_ℂ = ⟪x, bop (graph μ ρ w₀) y⟫_ℂ := by
    intro x y
    have e0 := hsa (WithLp.toLp 2 (x, (0 : Lp ℂ 2 μ))) (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply] at e0
    have e1 : ⟪((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x, (0 : Lp ℂ 2 μ)))).fst, y⟫_ℂ
        + ⟪((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x, (0 : Lp ℂ 2 μ)))).snd, (0 : Lp ℂ 2 μ)⟫_ℂ
        = ⟪x, ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))).fst⟫_ℂ
        + ⟪(0 : Lp ℂ 2 μ), ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))).snd⟫_ℂ := e0
    simp only [inner_zero_right, inner_zero_left, add_zero] at e1
    rw [bop_apply, bop_apply]
    exact e1
  have hSA : IsSelfAdjoint (bop (graph μ ρ w₀)) := by
    show star (bop (graph μ ρ w₀)) = bop (graph μ ρ w₀)
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr hsym).symm
  have hcomm : ∀ g, Commute (bop (graph μ ρ w₀)) (ρ g) := by
    intro g
    show bop (graph μ ρ w₀) * ρ g = ρ g * bop (graph μ ρ w₀)
    refine ContinuousLinearMap.ext (fun x => ?_)
    show bop (graph μ ρ w₀) (ρ g x) = ρ g (bop (graph μ ρ w₀) x)
    have hu : (WithLp.toLp 2 (ρ g x, (0 : Lp ℂ 2 μ)) : WithLp 2 (H × Lp ℂ 2 μ))
        = act ρ hR g (WithLp.toLp 2 (x, (0 : Lp ℂ 2 μ))) := by
      show _ = WithLp.toLp 2 (ρ g x, rt hR g 0)
      rw [map_zero]
    rw [bop_apply, bop_apply, hu, proj_act hR hone hmul hiso w₀ g]
    rfl
  have hD : ∀ y : H, MemLp (fun g => ⟪w₀, ρ g (bop (graph μ ρ w₀) y)⟫_ℂ) 2 μ := by
    intro y
    have hm' : ((((graph μ ρ w₀).starProjection (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))).snd : G → ℂ)) =ᵐ[μ]
        fun g => ⟪w₀, ρ g ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))).fst⟫_ℂ :=
      hmemP (WithLp.toLp 2 (y, (0 : Lp ℂ 2 μ)))
    rw [bop_apply]
    exact (Lp.memLp _).ae_eq hm'
  have hz : (WithLp.toLp 2 (x₀, MemLp.toLp _ h0) : WithLp 2 (H × Lp ℂ 2 μ)) ∈ graph μ ρ w₀ := by
    show ((MemLp.toLp _ h0 : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => ⟪w₀, ρ g x₀⟫_ℂ
    exact MemLp.coeFn_toLp h0
  have hne0 : bop (graph μ ρ w₀) x₀ ≠ 0 := by
    intro hB0
    have hf0 : ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).fst = 0 := by
      rw [← bop_apply]
      exact hB0
    have hs0 : ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).snd = 0 := by
      apply Lp.ext
      have h1 : ((((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).snd : G → ℂ)) =ᵐ[μ]
          fun g => ⟪w₀, ρ g ((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).fst⟫_ℂ :=
        hmemP (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))
      rw [hf0] at h1
      refine h1.trans ?_
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with g hg
      rw [hg, map_zero, inner_zero_right]
      rfl
    have hPz : (graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, MemLp.toLp _ h0))
        = WithLp.toLp 2 (x₀, MemLp.toLp _ h0) := by
      first
      | exact Submodule.starProjection_eq_self_iff.mpr hz
      | exact (Submodule.starProjection_eq_self_iff _).mpr hz
      | (rw [Submodule.starProjection_apply, Submodule.orthogonalProjection_mem_subspace_eq_self ⟨_, hz⟩])
    have e0 := hsa (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ))) (WithLp.toLp 2 (x₀, MemLp.toLp _ h0))
    rw [hPz, WithLp.prod_inner_apply, WithLp.prod_inner_apply] at e0
    have e1 : ⟪((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).fst, x₀⟫_ℂ
        + ⟪((graph μ ρ w₀).starProjection (WithLp.toLp 2 (x₀, (0 : Lp ℂ 2 μ)))).snd, MemLp.toLp _ h0⟫_ℂ
        = ⟪x₀, x₀⟫_ℂ + ⟪(0 : Lp ℂ 2 μ), MemLp.toLp _ h0⟫_ℂ := e0
    rw [hf0, hs0] at e1
    simp only [inner_zero_left, add_zero] at e1
    exact hx₀ (inner_self_eq_zero.mp e1.symm)
  obtain ⟨c, hc⟩ := schur (bop (graph μ ρ w₀)) hSA hcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne0
    rw [hc, map_zero, ContinuousLinearMap.zero_apply]
  have hx : bop (graph μ ρ w₀) (c⁻¹ • x) = x := by
    rw [hc, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hfin := hD (c⁻¹ • x)
  rw [hx] at hfin
  exact hfin

end Main

end ReciprocityTheory.ChartRestriction.DS.GraphTrick
