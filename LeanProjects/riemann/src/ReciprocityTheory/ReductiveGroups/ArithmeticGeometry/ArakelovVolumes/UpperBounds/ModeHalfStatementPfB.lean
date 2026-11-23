import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfB

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Nid (r : ℕ) : Fin r → Fin r → ℂ := fun a b => if a = b then 1 else 0

theorem of_Nid : Matrix.of (Nid r) = 1 := by
  ext a b
  simp [Nid, Matrix.one_apply]

theorem chosenFrame_isOrthogonal (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

private theorem sum_castLE_lemma {p0 : ℕ} (hp : p0 ≤ r) (f : Fin r → ℝ) :
    ∑ a : Fin p0, f (Fin.castLE hp a) = ∑ k : Fin r, if (k : ℕ) < p0 then f k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hp a) ?_ ?_ ?_ ?_
  · intro a _
    simp [a.2]
  · intro a _ b _ h
    exact Fin.castLE_injective hp h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl

theorem Ms_id (X : Data E r) (τ : X.Ψ) (v : Fin r → ℂ) :
    Ms X.p0 X.p0_le (Nid r) v = ∑ k, ‖v k‖ ^ 2 := by
  have hA : Ag X.p0 X.p0_le (Nid r) = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, sf, cl, Nid, Matrix.one_apply]
    rw [Finset.sum_eq_single (Fin.castLE X.p0_le a)]
    · have hs : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      by_cases hab : a = b
      · subst hab; simp [hs, sgn, a.2]
      · have : Fin.castLE X.p0_le a ≠ Fin.castLE X.p0_le b := fun h => hab (Fin.castLE_injective X.p0_le h)
        simp [hab, this]
    · intro k _ hk; simp [hk]
    · simp
  have hsf : ∀ c : Fin r, sf X.p0 v (cl (Nid r) c) = ((sgn X.p0 c : ℝ) : ℂ) * v c := by
    intro c
    simp only [sf, cl, Nid]
    rw [Finset.sum_eq_single c]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hin : (∑ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le b)))) =
      ∑ a : Fin X.p0, ((Complex.normSq (v (Fin.castLE X.p0_le a)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, mul_one, hsf, map_mul, Complex.conj_ofReal]
      have : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      rw [this]
      push_cast
      rw [one_mul, one_mul, Complex.mul_conj]
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), mul_zero, zero_mul]
    · simp
  have hvv : (sf X.p0 v v).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * Complex.normSq (v k) := by
    simp only [sf, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [Ms, hA, inv_one]
  rw [hin, hvv, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [sum_castLE_lemma X.p0_le (fun k => Complex.normSq (v k)), Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Complex.sq_norm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn]
  split_ifs <;> ring

theorem sf_smul_left (p0 : ℕ) (c : ℝ) (α β : Fin r → ℂ) :
    sf p0 ((c : ℂ) • α) β = c * sf p0 α β := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sf_smul_right (p0 : ℕ) (c : ℝ) (α β : Fin r → ℂ) :
    sf p0 α ((c : ℂ) • β) = c * sf p0 α β := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem Ms_smul (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (c : ℝ) (v : Fin r → ℂ) :
    Ms p0 hp N ((c : ℂ) • v) = c ^ 2 * Ms p0 hp N v := by
  have h1 : (∑ a : Fin p0, ∑ b : Fin p0, sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp a)) *
      (Ag p0 hp N)⁻¹ a b * conj (sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp b)))) =
      ((c ^ 2 : ℝ) : ℂ) * ∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) *
        (Ag p0 hp N)⁻¹ a b * conj (sf p0 v (cl N (Fin.castLE hp b))) := by
    simp only [sf_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have h2 : sf p0 ((c : ℂ) • v) ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * sf p0 v v := by
    rw [sf_smul_left, sf_smul_right]
    push_cast
    ring
  simp only [Ms]
  rw [h1, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

noncomputable def Mt (p0 : ℕ) (hp : p0 ≤ r) (q : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 q.1 (cl q.2.1 (Fin.castLE hp a)) * q.2.2 a b *
    conj (sf p0 q.1 (cl q.2.1 (Fin.castLE hp b)))).re - (sf p0 q.1 q.1).re

private theorem continuous_sf {T : Type*} [TopologicalSpace T] (p0 : ℕ) {f g : T → Fin r → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sf p0 (f x) (g x) := by
  simp only [sf]
  exact continuous_finset_sum _ fun k _ =>
    (continuous_const.mul ((continuous_apply k).comp hf)).mul
      (Complex.continuous_conj.comp ((continuous_apply k).comp hg))

theorem Mt_cont (p0 : ℕ) (hp : p0 ≤ r) : Continuous (Mt p0 hp) := by
  have hc : ∀ c : Fin r, Continuous fun q : (Fin r → ℂ) × (Fin r → Fin r → ℂ) ×
      Matrix (Fin p0) (Fin p0) ℂ => sf p0 q.1 (cl q.2.1 c) := fun c =>
    continuous_sf p0 continuous_fst
      (continuous_pi fun k => (continuous_apply c).comp ((continuous_apply k).comp continuous_snd.fst))
  unfold Mt
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ =>
    continuous_finset_sum _ fun b _ =>
      ((hc _).mul ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd.snd))).mul
        (Complex.continuous_conj.comp (hc _))))).sub
    (Complex.continuous_re.comp (continuous_sf p0 continuous_fst continuous_fst))

theorem Ag_cont (p0 : ℕ) (hp : p0 ≤ r) : Continuous (Ag p0 hp) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Ag, Matrix.of_apply]
  exact continuous_sf p0 (continuous_pi fun k => (continuous_apply _).comp (continuous_apply k))
    (continuous_pi fun k => (continuous_apply _).comp (continuous_apply k))

theorem Ag_Nid (p0 : ℕ) (hp : p0 ≤ r) : Ag p0 hp (Nid r) = 1 := by
  ext a b
  simp only [Ag, Matrix.of_apply, sf, cl, Nid, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castLE hp a)]
  · have hs : sgn p0 ((Fin.castLE hp a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
    by_cases hab : a = b
    · subst hab; simp [hs, sgn, a.2]
    · have : Fin.castLE hp a ≠ Fin.castLE hp b := fun h => hab (Fin.castLE_injective hp h)
      simp [hab, this]
  · intro k _ hk; simp [hk]
  · simp

theorem Ms_contAt (p0 : ℕ) (hp : p0 ≤ r) (v0 : Fin r → ℂ) :
    ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) (Nid r, v0) := by
  have hinv : ContinuousAt (fun M : Matrix (Fin p0) (Fin p0) ℂ => M⁻¹) (Ag p0 hp (Nid r)) := by
    rw [Ag_Nid]
    apply continuousAt_matrix_inv
    rw [Matrix.det_one]
    have := NormedRing.inverse_continuousAt (1 : ℂˣ)
    rwa [Units.val_one] at this
  have hAg : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ag p0 hp p.1) (Nid r, v0) :=
    ((Ag_cont p0 hp).comp continuous_fst).continuousAt
  have h1 : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) =>
      ((p.2, p.1, (Ag p0 hp p.1)⁻¹) : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ))
      (Nid r, v0) :=
    continuous_snd.continuousAt.prodMk
      (continuous_fst.continuousAt.prodMk (ContinuousAt.comp_of_eq hinv hAg rfl))
  have heq : (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) =
      fun p => Mt p0 hp (p.2, p.1, (Ag p0 hp p.1)⁻¹) := by
    funext p
    simp only [Ms, Mt]
  rw [heq]
  exact (Mt_cont p0 hp).continuousAt.comp h1

theorem Ms_zero (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Ms p0 hp N 0 = 0 := by
  simp [Ms, sf]

theorem Ms_unif (X : Data E r) (τ : X.Ψ) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ N in 𝓝 (Nid r), ∀ v : Fin r → ℂ, κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le N v ∧
      Ms X.p0 X.p0_le N v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by
  set S : Set (Fin r → ℂ) := {v | ∑ k, ‖v k‖ ^ 2 = 1} with hS
  have hScont : Continuous fun v : Fin r → ℂ => ∑ k, ‖v k‖ ^ 2 :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).norm).pow 2
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_eq hScont continuous_const)
    refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℂ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖v k‖ ^ 2 ≤ 1 := by
      have hv' : ∑ k, ‖v k‖ ^ 2 = 1 := hv
      rw [← hv']
      exact Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ k)
    nlinarith [norm_nonneg (v k)]
  have hev : ∀ᶠ N in 𝓝 (Nid r), ∀ v ∈ S,
      κ⁻¹ < Ms X.p0 X.p0_le N v ∧ Ms X.p0 X.p0_le N v < κ := by
    apply hSc.eventually_forall_of_forall_eventually
    intro v0 hv0
    have hc := Ms_contAt X.p0 X.p0_le v0
    have hval : Ms X.p0 X.p0_le (Nid r) v0 = 1 := by
      rw [Ms_id X τ]
      exact hv0
    have hmem : Set.Ioo κ⁻¹ κ ∈ 𝓝 (Ms X.p0 X.p0_le (Nid r) v0) := by
      rw [hval]
      exact Ioo_mem_nhds (inv_lt_one_of_one_lt₀ hκ) hκ
    filter_upwards [hc.preimage_mem_nhds hmem] with p hp
    exact hp
  filter_upwards [hev] with N hN
  intro v
  by_cases hv : ∑ k, ‖v k‖ ^ 2 = 0
  · have hv0 : v = 0 := by
      funext k
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp hv k
        (Finset.mem_univ k)
      simpa using h
    subst hv0
    simp [Ms_zero]
  · have hpos : 0 < ∑ k, ‖v k‖ ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hv)
    set s := Real.sqrt (∑ k, ‖v k‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
    have hss : s ^ 2 = ∑ k, ‖v k‖ ^ 2 := Real.sq_sqrt hpos.le
    set u : Fin r → ℂ := ((s⁻¹ : ℝ) : ℂ) • v with hu
    have huS : u ∈ S := by
      show ∑ k, ‖u k‖ ^ 2 = 1
      have hk : ∀ k, ‖u k‖ ^ 2 = s⁻¹ ^ 2 * ‖v k‖ ^ 2 := by
        intro k
        simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs0), mul_pow]
      simp only [hk, ← Finset.mul_sum, ← hss]
      field_simp
    have hvu : v = ((s : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_smul]
    have hMs : Ms X.p0 X.p0_le N v = s ^ 2 * Ms X.p0 X.p0_le N u := by
      rw [hvu, Ms_smul]
    obtain ⟨h1, h2⟩ := hN u huS
    rw [hMs, ← hss]
    have hs2 : 0 < s ^ 2 := pow_pos hs0 2
    constructor
    · nlinarith [mul_lt_mul_of_pos_left h1 hs2]
    · nlinarith [mul_lt_mul_of_pos_left h2 hs2]

theorem nmat_cont (X : Data E r) (τ : X.Ψ) : Continuous fun z : V (nd X) => nmat X z τ := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h1 : b < a
  · simp only [nmat, dif_pos h1]
    first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · simp only [nmat, dif_neg h1]
    exact continuous_const

theorem nmat_zero (X : Data E r) (τ : X.Ψ) : nmat X 0 τ = Nid r := by
  funext a b
  by_cases h1 : b < a
  · simp only [nmat, Nid, dif_pos h1, if_neg h1.ne']
    first
      | rfl
      | simp
  · simp [nmat, Nid, h1]

theorem ball_cmp (X : Data E r) {κ : ℝ} (hκ : 1 < κ) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ u, IsOrth X u → ∀ z : V (nd X), ‖z‖ < ρ → ∀ τ (v : Fin r → ℂ),
      κ⁻¹ * X.maj u τ v ≤ X.maj (cpt X u z) τ v ∧ X.maj (cpt X u z) τ v ≤ κ * X.maj u τ v := by
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ : X.Ψ, ∀ v : Fin r → ℂ,
      κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le (nmat X z τ) v ∧
        Ms X.p0 X.p0_le (nmat X z τ) v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by
    rw [Filter.eventually_all]
    intro τ
    have hc : Tendsto (fun z => nmat X z τ) (𝓝 0) (𝓝 (Nid r)) := by
      have := (nmat_cont X τ).tendsto 0
      rwa [nmat_zero X τ] at this
    exact hc.eventually (Ms_unif X τ hκ)
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨min ρ0 1, lt_min hρ0 one_pos, min_le_right _ _, ?_⟩
  intro u hu z hz τ v
  have hz' : z ∈ Metric.ball (0 : V (nd X)) ρ0 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  obtain ⟨h1, h2⟩ := hball z hz' τ ((mat u τ)⁻¹ *ᵥ v)
  have hY := hu τ
  have e1 : X.maj (cpt X u z) τ v = Ms X.p0 X.p0_le (nmat X z τ) ((mat u τ)⁻¹ *ᵥ v) :=
    maj_chart X hY (nmat X z τ) rfl v
  have e2 : X.maj u τ v = ∑ k, ‖((mat u τ)⁻¹ *ᵥ v) k‖ ^ 2 := by
    rw [maj_chart X hY (Nid r) (by rw [of_Nid, Matrix.mul_one]) v, Ms_id X τ]
  rw [e1, e2]
  exact ⟨h1, h2⟩

end ModeHalfB

end ReciprocityTheory.ChartRestriction.G.AR.Up
