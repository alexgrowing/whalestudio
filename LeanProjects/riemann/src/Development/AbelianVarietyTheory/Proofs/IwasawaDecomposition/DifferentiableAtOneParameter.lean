import Mathlib

noncomputable section

open Filter Topology MeasureTheory

namespace GlobalTheory.LocWeil.DerComm

theorem _root_.GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter {A : Type} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (φ : ℝ → A) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hm : ∀ s t : ℝ, φ (s + t) = φ s * φ t) : DifferentiableAt ℝ φ 0 := by
  have hφ := hc
  have hadd := hm
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > (0 : ℝ), ∀ s : ℝ, |s| ≤ δ → ‖1 - φ s‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]; linarith
    have := h hs'
    rw [dist_eq_norm, h0, norm_sub_rev] at this
    exact this.le
  set E : A := δ⁻¹ • ∫ s in (0 : ℝ)..δ, (1 - φ s) with hE
  have hEn : ‖E‖ < 1 := by
    have hI : ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      apply hball
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [sub_zero, abs_of_pos hδ] at hI
    rw [hE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ < 1 := by field_simp; norm_num
  set G : ℝ → A := fun x => ∫ s in (0 : ℝ)..x, φ s with hG
  have hint : ∀ t : ℝ, φ t * (1 - E) = δ⁻¹ • (G (t + δ) - G t) := by
    intro t
    have hC : 1 - E = δ⁻¹ • ∫ s in (0 : ℝ)..δ, φ s := by
      rw [hE, intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hδ.ne',
        one_smul, sub_sub_cancel]
    rw [hC, mul_smul_comm, hG,
      intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]
    congr 1
    have key := (ContinuousLinearMap.mul ℝ A (φ t)).intervalIntegral_comp_comm
      (hφ.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at key
    rw [← key]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t]
    simp [add_comm]
  set u : Aˣ := Units.oneSub E hEn with hu
  have hrep : φ = fun t => (δ⁻¹ • (G (t + δ) - G t)) * ↑u⁻¹ := by
    funext t
    rw [← hint t]
    have : (1 - E : A) = ↑u := by rw [hu, Units.val_oneSub]
    rw [this, Units.mul_inv_cancel_right]
  have hGd : ∀ x : ℝ, DifferentiableAt ℝ G x := fun x =>
    (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  rw [hrep]
  have h1 : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
    (hGd (0 + δ)).comp (0 : ℝ) (differentiableAt_id.add_const δ)
  have h2 : DifferentiableAt ℝ (fun t => δ⁻¹ • (G (t + δ) - G t)) 0 :=
    by
      have h3 := (h1.sub (hGd 0)).const_smul δ⁻¹
      exact h3
  exact h2.mul_const _

theorem eq_zero_of_tendsto_deriv {g h : ℕ → ℝ → ℂ} {m : ℝ → ℂ} (hd : ∀ n s, HasDerivAt (g n) (h n s) s)
    (hc : ∀ n, Continuous (h n)) (hm : Continuous m) (hg : ∀ s, Tendsto (fun n => g n s) atTop (𝓝 0))
    (hh : ∀ s, Tendsto (fun n => h n s) atTop (𝓝 (m s))) : m = 0 := by
  have hden := dense_iUnion_interior_of_closed (f := fun k : ℕ => {s : ℝ | ∀ n, ‖h n s‖ ≤ k})
    (fun k => by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun n => isClosed_le (hc n).norm continuous_const)
    (Set.eq_univ_of_forall fun s => by
      obtain ⟨C, hC⟩ := (hh s).norm.bddAbove_range
      obtain ⟨k, hk⟩ := exists_nat_ge C
      exact Set.mem_iUnion.2 ⟨k, fun n => (hC ⟨n, rfl⟩).trans hk⟩)
  refine hm.ext_on hden continuous_const fun x hx => ?_
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hk)
  have h1 : (fun b => ∫ s in x..b, m s) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Metric.ball_mem_nhds x hr] with b hb'
    have h2 : Tendsto (fun n => ∫ s in x..b, h n s) atTop (𝓝 (∫ s in x..b, m s)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (k : ℝ))
        (Eventually.of_forall fun n => (hc n).aestronglyMeasurable)
        (Eventually.of_forall fun n => Eventually.of_forall fun s hs => hb ?_ n) intervalIntegrable_const
        (Eventually.of_forall fun s _ => hh s)
      exact (convex_ball x r).ordConnected.uIcc_subset (Metric.mem_ball_self hr) hb' (Set.uIoc_subset_uIcc hs)
    have h3 := (hg b).sub (hg x)
    rw [sub_zero] at h3
    refine tendsto_nhds_unique h2 (h3.congr fun n => ?_)
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd n s) ((hc n).intervalIntegrable _ _)).symm
  exact (hm.integral_hasStrictDerivAt x x).hasDerivAt.unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq h1)

theorem tendsto_quot {φ : ℝ → ℂ} {a : ℂ} (h : HasDerivAt φ a 0) :
    Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) * (φ (1 / ((n : ℝ) + 1)) - φ 0)) atTop (𝓝 a) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (Nat.one_div_pos_of_nat (n := n)).ne'⟩
  refine ((hasDerivAt_iff_tendsto_slope.1 h).comp h1).congr fun n => ?_
  rw [Function.comp_apply, slope_def_module, sub_zero, Complex.real_smul]

section Alg

variable {S U : Type} [AddCommGroup S] [Module ℂ S]

theorem deriv_swap (ℓ : ℝ → S →ₗ[ℂ] ℂ) (E : Module.End ℂ S) (hℓ : ∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (E Ψ)) s)
    (p : ℝ → S) (a b : S) (ha : ∀ s, HasDerivAt (fun t => ℓ s (p t)) (ℓ s a) 0)
    (hb : ∀ s, HasDerivAt (fun t => ℓ s (E (p t))) (ℓ s b) 0) : ℓ 0 b = ℓ 0 (E a) := by
  have hc : ∀ Ψ, Continuous fun s => ℓ s Ψ := fun Ψ => continuous_iff_continuousAt.2 fun s => (hℓ Ψ s).continuousAt
  let q : ℕ → S := fun n => (((1 / ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) • (p (1 / ((n : ℝ) + 1)) - p 0) - a
  have := eq_zero_of_tendsto_deriv (g := fun n s => ℓ s (q n)) (h := fun n s => ℓ s (E (q n)))
    (m := fun s => ℓ s (b - E a)) (fun n s => hℓ _ s) (fun n => hc _) (hc _)
    (fun s => by
      have h1 := (tendsto_quot (ha s)).sub_const (ℓ s a)
      rw [sub_self] at h1
      refine h1.congr fun n => ?_
      simp only [q, map_sub, map_smul, smul_eq_mul])
    (fun s => by
      rw [map_sub]
      refine ((tendsto_quot (hb s)).sub_const (ℓ s (E a))).congr fun n => ?_
      simp only [q, map_sub, map_smul, smul_eq_mul])
  have h2 := congrFun this 0
  simp only [map_sub, Pi.zero_apply] at h2
  exact sub_eq_zero.1 h2

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

theorem hasDerivAt_move (ℓ : S →ₗ[ℂ] ℂ) (d : U →ₗ[ℝ] Module.End ℂ S) (P : ℝ → Module.End ℂ S) (hP : P 0 = 1)
    (A : Module.End ℂ S) (Φ : S) (hA : ∀ u, HasDerivAt (fun t => ℓ (P t (d u Φ))) (ℓ (A (d u Φ))) 0)
    {c : ℝ → U} {c' : U} (hc : HasDerivAt c c' 0) :
    HasDerivAt (fun t => ℓ (P t (d (c t) Φ))) (ℓ (d c' Φ + A (d (c 0) Φ))) 0 := by
  let b := Module.finBasis ℝ U
  have e : ∀ (Q : Module.End ℂ S) (u : U), ℓ (Q (d u Φ)) = ∑ i, b.coord i u • ℓ (Q (d (b i) Φ)) := fun Q u => by
    conv_lhs => rw [← b.sum_repr u]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
      Module.Basis.coord_apply]
  have e1 := e 1 c'
  rw [Module.End.one_apply] at e1
  rw [map_add, e1, e A, add_comm, ← Finset.sum_add_distrib]
  simp only [e (P _) (c _)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have := ((LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc).smul (hA (b i))
  rw [hP] at this
  exact this

variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)

def DualBases : Prop := (∀ x, ∑ i, β (b' i) x • b i = x) ∧ ∀ x, ∑ i, β x (b i) • b' i = x

theorem exists_dualBases (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) :
    ∃ (n : ℕ) (b b' : Fin n → U), DualBases β b b' := by
  have hn : LinearMap.BilinForm.Nondegenerate β := ⟨hβ, fun y hy => hβ y fun x => by rw [hs, hy, neg_zero]⟩
  let b := Module.finBasis ℝ U
  let b' := LinearMap.BilinForm.dualBasis β hn b
  refine ⟨_, b, b', fun x => ?_, fun x => ?_⟩
  · conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]
    simp only [b', map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left]
    simp
  · conv_rhs => rw [← b'.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]

variable {β b b'}

theorem DualBases.sum_adjoint (h : DualBases β b b') {M : Type} [AddCommGroup M] [Module ℝ M] (B : U →ₗ[ℝ] U →ₗ[ℝ] M)
    (g g' : U → U) (hg : ∀ x y, β (g' x) y = β x (g y)) : ∑ i, B (g (b i)) (b' i) = ∑ i, B (b i) (g' (b' i)) := by
  have e1 : ∀ i, B (g (b i)) (b' i) = ∑ j, β (b' j) (g (b i)) • B (b j) (b' i) := fun i => by
    conv_lhs => rw [← h.1 (g (b i))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have e2 : ∀ j, B (b j) (g' (b' j)) = ∑ i, β (b' j) (g (b i)) • B (b j) (b' i) := fun j => by
    conv_lhs => rw [← h.2 (g' (b' j))]
    simp only [map_sum, map_smul, hg]
  simp only [e1, e2]
  exact Finset.sum_comm

def quad (d : U →ₗ[ℝ] Module.End ℂ S) (b b' : ι → U) (Y : U →ₗ[ℝ] U) : Module.End ℂ S := ∑ i, d (Y (b i)) * d (b' i)

variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

theorem quad_mem (b b' : ι → U) (Y : U →ₗ[ℝ] U) : quad d b b' Y ∈ Algebra.adjoin ℂ (Set.range d) :=
  sum_mem fun _ _ => mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)

theorem DualBases.quad_comm (h : DualBases β b b') (hs : ∀ x y, β y x = -β x y)
    (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
    (hY : ∀ x y, β (Y x) y = -β x (Y y)) (u : U) : quad d b b' Y * d u - d u * quad d b b' Y = (2 * κ) • d (Y u) := by
  have e : ∀ i, d (Y (b i)) * d (b' i) * d u - d u * (d (Y (b i)) * d (b' i)) =
      κ • d (Y (β (b' i) u • b i)) + κ • d (β (Y u) (b i) • b' i) := fun i => by
    have : d (Y (b i)) * d (b' i) * d u - d u * (d (Y (b i)) * d (b' i)) =
        d (Y (b i)) * (d (b' i) * d u - d u * d (b' i)) + (d (Y (b i)) * d u - d u * d (Y (b i))) * d (b' i) := by
      noncomm_ring
    rw [this, hd, hd, hY (b i), ← hs, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, map_smul, map_smul, map_smul,
      mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [quad, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← map_sum, ← map_sum, ← map_sum, h.1, h.2, two_mul,
    add_smul]

theorem DualBases.quad_group (h : DualBases β b b') (P : Module.End ℂ S) (g g' : U →ₗ[ℝ] U)
    (hP : ∀ u, P * d u = d (g u) * P) (hg : ∀ x y, β (g x) (g y) = β x y) (hg' : ∀ x, g (g' x) = x)
    (hc : ∀ x, g (Y x) = Y (g x)) : P * quad d b b' Y = quad d b b' Y * P := by
  have := h.sum_adjoint ((LinearMap.mul ℝ (Module.End ℂ S)).compl₁₂ (d ∘ₗ Y) (d ∘ₗ g)) g g'
    (fun x y => by rw [← hg, hg'])
  simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.mul_apply', hg'] at this
  rw [quad, Finset.mul_sum]
  conv_rhs => rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, hP, mul_assoc, hP, hc, mul_assoc]

theorem DualBases.quad_lie (h : DualBases β b b') {N : Submodule ℂ S} (hN : ∀ u, ∀ Φ ∈ N, d u Φ ∈ N)
    (A : Module.End ℂ S) (Z : U →ₗ[ℝ] U) (hA : ∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Z u) Φ + d u (A Φ))
    (hZ : ∀ x y, β (Z x) y = -β x (Z y)) (hc : ∀ x, Z (Y x) = Y (Z x)) :
    ∀ Φ ∈ N, A (quad d b b' Y Φ) = quad d b b' Y (A Φ) := by
  intro Φ hΦ
  have := h.sum_adjoint ((LinearMap.mul ℝ (Module.End ℂ S)).compl₁₂ (d ∘ₗ Y) d) Z (fun x => -Z x)
    (fun x y => by rw [map_neg, LinearMap.neg_apply, hZ, neg_neg])
  simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.mul_apply', map_neg, Finset.sum_neg_distrib] at this
  have h2 := LinearMap.congr_fun this Φ
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, Module.End.mul_apply] at h2
  simp only [quad, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hA _ _ (hN _ _ hΦ), hA _ _ hΦ, map_add, hc,
    Finset.sum_add_distrib, h2]
  abel

omit [FiniteDimensional ℝ U] in
theorem commute_deriv {φ : ℝ → U →L[ℝ] U} {Y Z : U →L[ℝ] U} (h : HasDerivAt φ Y 0) (hc : ∀ t, Commute Z (φ t)) :
    Commute Z Y :=
  (h.const_mul Z).unique ((h.mul_const Z).congr_of_eventuallyEq (Eventually.of_forall fun t => hc t))

section Main

variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)

include hN in
theorem apply_mem {a : Module.End ℂ S} (ha : a ∈ Algebra.adjoin ℂ (Set.range d)) : ∀ Φ ∈ N, a Φ ∈ N := fun Φ hΦ => by
  obtain ⟨a', ha', rfl⟩ := (hN Φ).1 hΦ
  exact (hN _).2 ⟨a * a', mul_mem ha ha', rfl⟩

include hN hvac in

theorem scalar_of_comm {B : Module.End ℂ S} (hB : B ∈ Algebra.adjoin ℂ (Set.range d))
    (hc : ∀ u, ∀ Φ ∈ N, B (d u Φ) = d u (B Φ)) : ∃ c : ℂ, ∀ Φ ∈ N, B Φ = c • Φ := by
  have hf : f ∈ N := (hN f).2 ⟨1, one_mem _, rfl⟩
  obtain ⟨c, h⟩ := hvac B hB fun u => hc u f hf
  have key : ∀ a ∈ Algebra.adjoin ℂ (Set.range d), ∀ Φ ∈ N, B (a Φ) = a (B Φ) := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact hc u
    | algebraMap r => exact fun Φ _ => map_smul B r Φ
    | add x y _ _ hx hy => exact fun Φ hΦ => by rw [LinearMap.add_apply, map_add, hx Φ hΦ, hy Φ hΦ, LinearMap.add_apply]
    | mul x y _ hy' hx hy =>
      exact fun Φ hΦ => by rw [Module.End.mul_apply, hx _ (apply_mem hN hy' Φ hΦ), hy Φ hΦ, Module.End.mul_apply]
  refine ⟨c, fun Φ hΦ => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (hN Φ).1 hΦ
  rw [key a ha f hf, h, map_smul]

include hs hκ hd hω hG hN hvac hev hline in

theorem exists_generator (hb : DualBases β b b') (p : ℝ → Γ) (h0 : p 0 = 1) (hm : ∀ s t, p (s + t) = p s * p t)
    (hc : Continuous fun t => G (p t)) {A : Module.End ℂ S} (hA : A ∈ Algebra.adjoin ℂ (Set.range d))
    (hder : ∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p t) Φ)) (ev w (A Φ)) 0) :
    ∃ Y : U →L[ℝ] U, HasDerivAt (fun t => G (p t)) Y 0 ∧ (∀ x y, β (Y x) y = -β x (Y y)) ∧
      (∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Y u) Φ + d u (A Φ)) ∧
      ∃ c : ℂ, ∀ Φ ∈ N, A Φ = (2 * κ)⁻¹ • quad d b b' Y.toLinearMap Φ + c • Φ := by
  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  have hY := (differentiableAt_oneParameter (fun t => G (p t)) hc (by rw [h0, map_one])
    (fun s t => by rw [hm, map_mul])).hasDerivAt
  set Y := deriv (fun t => G (p t)) 0
  have hYu : ∀ u, HasDerivAt (fun t => G (p t) u) (Y u) 0 := fun u => by
    simpa using hY.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have hdN : ∀ u, ∀ Φ ∈ N, d u Φ ∈ N := fun u => apply_mem hN (Algebra.subset_adjoin ⟨u, rfl⟩)
  have h1 : ∀ x y, β (Y x) y = -β x (Y y) := fun x y => by
    let β' : U →L[ℝ] U →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (U →ₗ[ℝ] ℝ) ≃ₗ[ℝ] U →L[ℝ] ℝ).toLinearMap ∘ₗ β)
    have h2 := (β'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hYu x)).clm_apply (hYu y)
    have h3 := h2.unique ((hasDerivAt_const (0 : ℝ) (β x y)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => hG (p t) x y))
    simp only [Function.comp_apply, h0, map_one, ContinuousLinearMap.one_apply] at h3
    exact eq_neg_of_add_eq_zero_left h3
  have h2 : ∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Y u) Φ + d u (A Φ) := fun u Φ hΦ => by
    have h3 : HasDerivAt (fun t => G (p (-t)) u) (-Y u) 0 := by
      have := HasDerivAt.scomp (0 : ℝ) (by rw [neg_zero]; exact hYu u) (hasDerivAt_neg (0 : ℝ))
      rw [neg_one_smul] at this
      exact this
    have h4 : ∀ t, ω (p t) (d (G (p (-t)) u) Φ) = d u (ω (p t) Φ) := fun t => by
      rw [← Module.End.mul_apply, hω, ← ContinuousLinearMap.mul_apply, ← map_mul, ← hm, add_neg_cancel, h0, map_one]
      rfl
    have h5 : d (-Y u) Φ + A (d u Φ) = d u (A Φ) := hev _ _ fun w => by
      obtain ⟨ℓ, hl0, hl1, hl2⟩ := hline w u
      have h6 : ∀ s, ∀ Ψ ∈ N, HasDerivAt (fun t => ℓ s (ω (p t) Ψ)) (ℓ s (A Ψ)) 0 := fun s Ψ hΨ => by
        obtain ⟨c, w', e⟩ := hl2 s
        simp only [e]
        exact (hder Ψ hΨ w').const_mul c
      rw [← hl0]
      refine deriv_swap ℓ (d u) hl1 (fun t => ω (p t) Φ) _ _ (fun s => h6 s Φ hΦ) fun s => ?_
      have := hasDerivAt_move (ℓ s) d (fun t => ω (p t)) (by rw [h0, map_one]) A Φ
        (fun v => h6 s _ (hdN v Φ hΦ)) h3
      simp only [h4, neg_zero, h0, map_one, ContinuousLinearMap.one_apply] at this
      exact this
    rw [← h5, map_neg, LinearMap.neg_apply, add_neg_cancel_left]
  refine ⟨Y, hY, h1, h2, ?_⟩
  obtain ⟨c, hc⟩ := scalar_of_comm hN hvac (sub_mem hA (Subalgebra.smul_mem _ (quad_mem b b' Y.toLinearMap) (2 * κ)⁻¹))
    (fun u Φ hΦ => by
      have := LinearMap.congr_fun (hb.quad_comm hs hd (Y := Y.toLinearMap) h1 u) Φ
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, sub_eq_iff_eq_add] at this
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, h2 u Φ hΦ, this, smul_add, smul_smul,
        inv_mul_cancel₀ (mul_ne_zero two_ne_zero hκ), one_smul, ContinuousLinearMap.coe_coe]
      abel)
  exact ⟨c, fun Φ hΦ => by rw [← hc Φ hΦ, LinearMap.sub_apply, LinearMap.smul_apply, add_sub_cancel]⟩

include hβ hs hκ hd hω hG hN hvac hev hline in

theorem der_comm (p : ℝ → Γ) (h0 : p 0 = 1) (hm : ∀ s t, p (s + t) = p s * p t)
    (hc : Continuous fun t => G (p t)) {A : Module.End ℂ S} (hA : A ∈ Algebra.adjoin ℂ (Set.range d))
    (hder : ∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p t) Φ)) (ev w (A Φ)) 0) :
    (∀ k, (∀ t, Commute k (p t)) → (∀ Φ ∈ N, ω k Φ ∈ N) → ∀ Φ ∈ N, A (ω k Φ) = ω k (A Φ)) ∧
    ∀ p' : ℝ → Γ, p' 0 = 1 → (∀ s t, p' (s + t) = p' s * p' t) → (Continuous fun t => G (p' t)) →
      ∀ A' ∈ Algebra.adjoin ℂ (Set.range d),
      (∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p' t) Φ)) (ev w (A' Φ)) 0) → (∀ s t, Commute (p s) (p' t)) →
      ∀ Φ ∈ N, A (A' Φ) = A' (A Φ) := by
  obtain ⟨n, b, b', hb⟩ := exists_dualBases β hβ hs
  obtain ⟨Y, hY, -, -, c, hc⟩ := exists_generator ω G ev hs hκ hd hω hG hN hvac hev hline hb p h0 hm hc hA hder
  refine ⟨fun k hk hkN Φ hΦ => ?_, fun p' h0' hm' hc' A' hA' hder' hcc Φ hΦ => ?_⟩
  · have h1 := commute_deriv hY fun t => (hk t).map G
    have h2 := hb.quad_group (Y := Y.toLinearMap) (ω k) (G k).toLinearMap (G k⁻¹).toLinearMap (hω k) (hG k)
      (fun x => by
        change (G k * G k⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl) fun x => ContinuousLinearMap.ext_iff.1 h1 x
    rw [hc _ (hkN Φ hΦ), hc Φ hΦ, map_add, map_smul, map_smul, ← Module.End.mul_apply, ← h2, Module.End.mul_apply]
  · obtain ⟨Z, hZ, h1, h2, -⟩ := exists_generator ω G ev hs hκ hd hω hG hN hvac hev hline hb p' h0' hm' hc' hA' hder'
    have h3 := commute_deriv hY fun s => (commute_deriv hZ fun t => (hcc s t).map G).symm
    have h4 := hb.quad_lie (Y := Y.toLinearMap) (fun u => apply_mem hN (Algebra.subset_adjoin ⟨u, rfl⟩)) A'
      Z.toLinearMap h2 h1 (fun x => ContinuousLinearMap.ext_iff.1 h3 x) Φ hΦ
    rw [hc _ (apply_mem hN hA' Φ hΦ), hc Φ hΦ, map_add, map_smul, map_smul, h4]

end Main

end Alg

end GlobalTheory.LocWeil.DerComm

end
