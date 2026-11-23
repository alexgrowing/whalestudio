import Development.WeilBound.ThetaLifts.LatticeBasics.SWFull

noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open Filter Topology Metric
open scoped BoundedContinuousFunction

variable {X : Type} {h : X → ℝ}

theorem unif_bound (h1 : ∀ x, 1 ≤ h x) {V : Submodule ℂ (X → ℂ)} (hV : ∀ f ∈ V, ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * h x ^ N)
    {D : Set ℂ} {H : ℂ → V} (hb : ∀ μ : V →ₗ[ℂ] ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C) →
      ∃ C, ∀ s ∈ D, ‖μ (H s)‖ ≤ C) : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ D, ∀ x, ‖(H s).1 x‖ ≤ C * h x ^ N := by
  by_contra hn
  push Not at hn
  choose s hs g hg using fun n : ℕ => hn (n * 2 ^ n) n
  have h0 : ∀ x, 0 < h x := fun x => one_pos.trans_le (h1 x)
  let w : ℕ → ℝ := fun n => (1 / 2) ^ n / h (g n) ^ n
  have w0 : ∀ n, 0 < w n := fun n => div_pos (by positivity) (pow_pos (h0 _) _)
  have est : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ (c : ℕ →ᵇ ℂ) n,
      ‖c n * (w n * f (g n))‖ ≤ C * K * ‖c‖ * (1 / 2) ^ n := fun N => by
    refine ⟨1 + ∑ m ∈ Finset.range N, h (g m) ^ N, fun f C hf c n => ?_⟩
    have C0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf (g n))) (pow_pos (h0 _) _)
    have S0 : 0 ≤ ∑ m ∈ Finset.range N, h (g m) ^ N := Finset.sum_nonneg fun m _ => (pow_pos (h0 _) _).le
    have k : h (g n) ^ N / h (g n) ^ n ≤ 1 + ∑ m ∈ Finset.range N, h (g m) ^ N := by
      by_cases hN : n < N
      · refine (div_le_self (pow_pos (h0 _) _).le (one_le_pow₀ (h1 _))).trans (le_add_of_nonneg_of_le zero_le_one ?_)
        exact Finset.single_le_sum (f := fun m => h (g m) ^ N) (fun m _ => (pow_pos (h0 _) _).le) (Finset.mem_range.2 hN)
      · exact ((div_le_one (pow_pos (h0 _) _)).2 (pow_le_pow_right₀ (h1 _) (not_lt.1 hN))).trans (le_add_of_nonneg_right S0)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le]
    calc _ ≤ ‖c‖ * (w n * (C * h (g n) ^ N)) := by gcongr; exacts [mul_nonneg (w0 n).le (norm_nonneg _), c.norm_coe_le_norm n, (w0 n).le, hf _]
      _ = C * (h (g n) ^ N / h (g n) ^ n) * ‖c‖ * (1 / 2) ^ n := by simp only [w]; ring
      _ ≤ _ := by gcongr
  have sm : ∀ (f : V) (c : ℕ →ᵇ ℂ), Summable fun n => c n * (w n * f.1 (g n)) := fun f c => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := est N
    exact .of_norm_bounded (summable_geometric_two.mul_left _) (hK f C hf c)
  have bd : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ c : ℕ →ᵇ ℂ,
      ‖∑' n, c n * (w n * f (g n))‖ ≤ C * K * 2 * ‖c‖ := fun N => (est N).imp fun K hK f C hf c =>
    (tsum_of_norm_bounded (hasSum_geometric_two.mul_left _) (hK f C hf c)).trans_eq (by ring)
  let B : V →ₗ[ℂ] (ℕ →ᵇ ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun f c => ∑' n, c n * (w n * f.1 (g n)))
    (fun f f' c => by rw [← (sm f c).tsum_add (sm f' c)]; simp [mul_add])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
    (fun f c c' => by rw [← (sm f c).tsum_add (sm f c')]; simp [add_mul])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
  have ct : ∀ f : V, ∃ C, ∀ c, ‖B f c‖ ≤ C * ‖c‖ := fun f => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := bd N
    exact ⟨_, hK f C hf⟩
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun n : ℕ => (B (H (s n))).mkContinuousOfExistsBound (ct _)) fun c => by
    obtain ⟨C, hC⟩ := hb (B.flip c) fun N => (bd N).elim fun K hK => ⟨_, fun f hf => hK f 1 (by simpa using hf) c⟩
    exact ⟨C, fun n => hC _ (hs n)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 0)
  let c : ℕ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (Pi.single n 1) 1 fun m => by
    by_cases e : m = n <;> simp [e]
  have c1 : ‖c‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).2 fun m => by by_cases e : m = n <;> simp [c, e]
  have e1 : ‖B (H (s n)) c‖ ≤ max M 0 :=
    (ContinuousLinearMap.le_of_opNorm_le _ ((hM n).trans (le_max_left M 0)) c).trans (mul_le_of_le_one_right (le_max_right _ _) c1)
  have e2 : B (H (s n)) c = w n * (H (s n)).1 (g n) :=
    (tsum_eq_single n fun m e => by simp [c, e]).trans (by simp [c])
  rw [e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le] at e1
  have e3 : w n * (n * 2 ^ n * h (g n) ^ n) = n := by
    have := (h0 (g n)).ne'
    simp only [w, one_div, inv_pow]; field_simp
  linarith [mul_lt_mul_of_pos_left (hg n) (w0 n)]

variable [TopologicalSpace X] {g g' : ℂ → X → ℂ} {S S' : Set ℂ} {s₀ : ℂ}

variable (h g S) in

structure RegOn : Prop where
  hol : ∀ x, DifferentiableOn ℂ (g · x) S
  cont : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (S ×ˢ Set.univ)
  grow : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N

variable (h g s₀) in

def Reg : Prop := ∃ S ∈ 𝓝 s₀, RegOn h g S

theorem RegOn.mono (a : RegOn h g S) (e : S' ⊆ S) : RegOn h g S' :=
  ⟨fun x => (a.hol x).mono e, a.cont.mono (Set.prod_mono e subset_rfl), a.grow.imp fun _ => .imp fun _ b s hs => b s (e hs)⟩

theorem Reg.congr (a : Reg h g s₀) (e : g' =ᶠ[𝓝 s₀] g) : Reg h g' s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have b := a.mono (Set.inter_subset_left (t := {s | g' s = g s}))
  exact ⟨_, inter_mem hS e, fun x => (b.hol x).congr fun s hs => congrFun hs.2 x, b.cont.congr fun y hy => congrFun hy.1.2 y.2,
    b.grow.imp fun _ => .imp fun _ b s hs x => by rw [hs.2]; exact b s hs x⟩

theorem Reg.eventually (a : Reg h g s₀) : ∀ᶠ s in 𝓝 s₀, Reg h g s :=
  let ⟨S, hS, a⟩ := a
  (eventually_mem_nhds_iff.2 hS).mono fun _ hs => ⟨S, hs, a⟩

theorem Reg.contAt (a : Reg h g s₀) (x : X) : ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x) :=
  let ⟨_, hS, a⟩ := a
  a.cont.continuousAt (prod_mem_nhds hS univ_mem)

theorem Reg.mul (h1 : ∀ x, 1 ≤ h x) (a : Reg h g s₀) {c : ℂ → ℂ} (hc : AnalyticAt ℂ c s₀) {u : X → X} (hu : Continuous u) {b : ℝ}
    (hb : ∀ x, h (u x) ≤ b * h x) : Reg h (fun s x => c s * g s (u x)) s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have e : ∀ᶠ s in 𝓝 s₀, ‖c s‖ < ‖c s₀‖ + 1 := hc.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨_, inter_mem hS (hc.eventually_analyticAt.and e), fun x => DifferentiableOn.mul
    (fun s hs => hs.2.1.differentiableAt.differentiableWithinAt) ((a.hol (u x)).mono Set.inter_subset_left),
    ContinuousOn.mul (fun y hy => (hy.1.2.1.continuousAt.comp continuous_fst.continuousAt).continuousWithinAt)
      (a.cont.comp (f := fun y : ℂ × X => (y.1, u y.2)) (by fun_prop) fun y hy => ⟨hy.1.1, trivial⟩), ?_⟩
  obtain ⟨C, N, hC⟩ := a.grow
  refine ⟨(‖c s₀‖ + 1) * (max C 0 * b ^ N), N, fun s hs x => ?_⟩
  have h0 := zero_le_one.trans (h1 (u x))
  rw [norm_mul, mul_assoc, mul_assoc, ← mul_pow]
  exact mul_le_mul hs.2.2.le ((hC s hs.1 _).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (hb x) N) (pow_nonneg h0 _)
    (le_max_right _ _))) (norm_nonneg _) (by positivity)

theorem reg_of_bound (hh : Continuous h) (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) (hc : ∀ s ∈ S, Continuous (g s))
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N) : Reg h g s₀ := by
  refine ⟨interior S, interior_mem_nhds.2 hS, fun x => (hd x).mono interior_subset, fun y hy => ContinuousAt.continuousWithinAt ?_,
    hg.imp fun _ => .imp fun _ b s hs => b s (interior_subset hs)⟩
  obtain ⟨C, N, hC⟩ := hg
  obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy.1)
  have : Tendsto (fun z : ℂ × X => g z.1 z.2 - g y.1 z.2) (𝓝 y) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun z => 2 * (C * h z.2 ^ N) / r * dist z.1 y.1) ?_ ?_
    · filter_upwards [continuous_fst.continuousAt.eventually (ball_mem_nhds y.1 r0)] with z hz
      rw [← dist_eq_norm]
      refine Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := (g · z.2)) ((hd z.2).mono hr) (fun s hs => ?_) hz
      rw [mem_closedBall, dist_eq_norm, two_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hC s (hr hs) _) (hC _ (hr (mem_ball_self r0)) _))
    · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  simpa [ContinuousAt] using this.add ((hc _ (interior_subset hy.1)).comp continuous_snd).continuousAt

theorem Reg.punct (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x) :
    ∀ᶠ s in 𝓝[≠] s₀, Reg h g s := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds a.eventually, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_nhdsWithin_iff.1 e).eventually_nhds] with s b hs e
  refine (b.mul h1 (c := fun z => ((z - s₀) ^ k)⁻¹) (AnalyticAt.inv (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hs)))
    continuous_id (b := 1) (by simp)).congr ?_
  filter_upwards [e, isOpen_ne.mem_nhds hs] with z hz hz'
  funext x
  rw [id, hz hz', inv_mul_cancel_left₀ (pow_ne_zero _ (sub_ne_zero.2 hz'))]

theorem Reg.remove (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x)
    (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) : Reg h g s₀ := by
  obtain ⟨S', hS', b⟩ := id a
  obtain ⟨ρ, ρ0, hρ⟩ := nhds_basis_closedBall.mem_iff.1
    (inter_mem (inter_mem hS hS') (eventually_nhdsWithin_iff.1 (e.and (a.punct h1 e))))
  have dc : ∀ x, DiffContOnCl ℂ (g · x) (ball s₀ ρ) := fun x => (hd x).diffContOnCl_ball fun z hz => (hρ hz).1.1
  have sp : ∀ z ∈ sphere s₀ ρ, z ≠ s₀ := fun z hz => ne_of_mem_sphere hz ρ0.ne'
  obtain ⟨C, N, hC⟩ := b.grow
  refine ⟨_, ball_mem_nhds s₀ ρ0, fun x => (dc x).differentiableOn, fun y hy => ContinuousAt.continuousWithinAt ?_, C / ρ ^ k, N,
    fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (dc x) (fun w hw => ?_) (subset_closure hz)⟩
  · by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (((hρ (sphere_subset_closedBall hz.1)).2 (sp _ hz.1)).2.contAt z.2).continuousWithinAt) _
    · exact ((hρ (ball_subset_closedBall hy.1)).2 e0).2.contAt y.2
  · rw [frontier_ball _ ρ0.ne'] at hw
    have c := hρ (sphere_subset_closedBall hw)
    have := hC w c.1.2 x
    rw [(c.2 (sp w hw)).1, norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
    rw [div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
    exact this

theorem preconn {U : Set ℂ} (hU : ∀ s, ∀ᶠ z in 𝓝[≠] s, z ∈ U) : IsPreconnected U := by
  obtain ⟨t, ht, -, hc⟩ := isLindelof_univ.elim_nhds_subcover (fun s => insert s U) fun s _ => insert_mem_nhds_iff.2 (hU s)
  have : (Uᶜ).Countable := ht.mono fun z hz => by
    obtain ⟨s, hs, e⟩ := Set.mem_iUnion₂.1 (hc (Set.mem_univ z))
    exact e.resolve_right hz ▸ hs
  simpa using (this.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

end GlobalTheory.ThK.Dbl.An

end
