import Mathlib

noncomputable section

namespace PositivityTheory.ThKEst.LinDerPf

open Filter Topology Asymptotics

section Step

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem step (β : Multiplicative ℝ →* H) (hβ : Continuous β) (f f' : H → ℂ) (hf' : Continuous f')
    (hd : ∀ h, HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t))) (f' h) 0)
    (p : ℝ → H) (hp : ContinuousAt p 0) (u : ℝ → ℝ) (u' : ℝ) (hu : HasDerivAt u u' 0) (hu0 : u 0 = 0)
    (D : ℂ) (hD : HasDerivAt (fun t => f (p t)) D 0) :
    HasDerivAt (fun t => f (p t * β (Multiplicative.ofAdd (u t)))) (D + u' * f' (p 0)) 0 := by
  have hd' : ∀ h (v : ℝ), HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t)))
      (f' (h * β (Multiplicative.ofAdd v))) v := fun h v => by
    have h1 := hd (h * β (Multiplicative.ofAdd v))
    have h2 : HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd v) * β (Multiplicative.ofAdd t)))
        (f' (h * β (Multiplicative.ofAdd v))) (v - v) := by rwa [sub_self]
    have h3 := h2.comp_sub_const v v
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  set R : ℝ → ℂ := fun t => f (p t * β (Multiplicative.ofAdd (u t))) - f (p t) - u t * f' (p 0) with hR
  have hc : Continuous fun z : H × ℝ => f' (z.1 * β (Multiplicative.ofAdd z.2)) :=
    hf'.comp (continuous_fst.mul (hβ.comp (continuous_ofAdd.comp continuous_snd)))
  have ho : R =o[𝓝 0] u := by
    refine isLittleO_iff.2 fun ε hε => ?_
    have h1 : ∀ᶠ z : H × ℝ in 𝓝 (p 0, 0), ‖f' (z.1 * β (Multiplicative.ofAdd z.2)) - f' (p 0)‖ ≤ ε := by
      have h2 := (hc.tendsto (p 0, 0))
      simp only [ofAdd_zero, map_one, mul_one] at h2
      filter_upwards [h2 (Metric.closedBall_mem_nhds _ hε)] with z hz
      simpa [dist_eq_norm] using hz
    rw [nhds_prod_eq] at h1
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.1 h1
    obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff_ball.1 hV
    have hu1 : ∀ᶠ t in 𝓝 (0 : ℝ), u t ∈ Metric.ball (0 : ℝ) δ := by
      have := hu.continuousAt.tendsto
      rw [hu0] at this
      exact this (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hp.tendsto hU, hu1] with t ht1 ht2
    have h3 := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v : ℝ => f (p t * β (Multiplicative.ofAdd v)) - v * f' (p 0))
      (f' := fun v : ℝ => f' (p t * β (Multiplicative.ofAdd v)) - f' (p 0)) (C := ε)
      (fun v _ => by
        have h4 : HasDerivAt (fun v : ℝ => (v : ℂ) * f' (p 0)) (f' (p 0)) v := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const (f' (p 0))
        exact ((hd' (p t) v).sub h4).hasDerivWithinAt)
      (fun v hv => hUV ht1 (hδV v hv)) (Metric.mem_ball_self hδ) ht2
    simp only [ofAdd_zero, map_one, mul_one, Complex.ofReal_zero, zero_mul, sub_zero] at h3
    have e : R t = f (p t * β (Multiplicative.ofAdd (u t))) - u t * f' (p 0) - f (p t) := by
      simp only [hR]
      ring
    rw [e]
    exact h3
  have hO : u =O[𝓝 0] fun t : ℝ => t - 0 := by
    have := hu.isBigO_sub
    simpa [hu0] using this
  have hR0 : HasDerivAt R 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    have : R 0 = 0 := by simp [hR, hu0]
    simpa [this] using ho.trans_isBigO hO
  have h5 : HasDerivAt (fun t : ℝ => (u t : ℂ) * f' (p 0)) (u' * f' (p 0)) 0 :=
    hu.ofReal_comp.mul_const _
  have h6 := (hR0.add hD).add h5
  rw [zero_add] at h6
  refine h6.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [hR, Pi.add_apply]
  ring

theorem chain (f : H → ℂ) : ∀ (m : ℕ) (β : Fin m → Multiplicative ℝ →* H) (_ : ∀ i, Continuous (β i))
    (f' : Fin m → H → ℂ) (_ : ∀ i, Continuous (f' i))
    (_ : ∀ i h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0)
    (p : ℝ → H) (_ : ContinuousAt p 0) (u : Fin m → ℝ → ℝ) (u' : Fin m → ℝ) (_ : ∀ i, HasDerivAt (u i) (u' i) 0)
    (_ : ∀ i, u i 0 = 0) (D : ℂ) (_ : HasDerivAt (fun t => f (p t)) D 0),
    HasDerivAt (fun t => f (p t * (List.ofFn fun i => β i (Multiplicative.ofAdd (u i t))).prod))
      (D + ∑ i, (u' i : ℂ) * f' i (p 0)) 0 := by
  intro m
  induction m with
  | zero =>
    intro β _ f' _ _ p _ u u' _ _ D hD
    simpa using hD
  | succ m ih =>
    intro β hβ f' hf' hd p hp u u' hu hu0 D hD
    have h1 := step (β 0) (hβ 0) f (f' 0) (hf' 0) (hd 0) p hp (u 0) (u' 0) (hu 0) (hu0 0) D hD
    have h2 := ih (fun i => β i.succ) (fun i => hβ _) (fun i => f' i.succ) (fun i => hf' _) (fun i => hd _)
      (fun t => p t * β 0 (Multiplicative.ofAdd (u 0 t)))
      (hp.mul (((hβ 0).comp continuous_ofAdd).continuousAt.comp (hu 0).continuousAt))
      (fun i => u i.succ) (fun i => u' i.succ) (fun i => hu _) (fun i => hu0 _) _ h1
    simp only [hu0, ofAdd_zero, map_one, mul_one] at h2
    simpa only [List.ofFn_succ, List.prod_cons, mul_assoc, Fin.sum_univ_succ, add_assoc] using h2

end Step

section Alg

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def Gr (a : A →L[ℝ] A) (g : A) : Prop := a g * g = 1 ∧ g * a g = 1

def pr (a : A →L[ℝ] A) : A →L[ℝ] A := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ A - a)

theorem pr_apply (a : A →L[ℝ] A) (x : A) : pr a x = (1 / 2 : ℝ) • (x - a x) := rfl

variable {a : A →L[ℝ] A}

theorem Gr.mul (ha : ∀ x y, a (x * y) = a y * a x) {g h : A} (hg : Gr a g) (hh : Gr a h) : Gr a (g * h) := by
  constructor
  · rw [ha, mul_assoc, ← mul_assoc (a g), hg.1, one_mul, hh.1]
  · rw [ha, mul_assoc, ← mul_assoc h, hh.2, one_mul, hg.2]

theorem Gr.list (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) (l : List A) (hl : ∀ g ∈ l, Gr a g) :
    Gr a l.prod := by
  induction l with
  | nil => simp [Gr, h1]
  | cons x l ih =>
    rw [List.prod_cons]
    exact (hl x (by simp)).mul ha (ih fun g hg => hl g (by simp [hg]))

theorem Gr.anti (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {g : A} (hg : Gr a g) :
    a (pr a g) = -pr a g := by
  have h2 : a g * a (a g) = 1 := by rw [← ha, hg.1, h1]
  have h3 : a (a g) = g := by
    calc a (a g) = (g * a g) * a (a g) := by rw [hg.2, one_mul]
      _ = g := by rw [mul_assoc, h2, mul_one]
  rw [pr_apply, map_smul, map_sub, h3, ← smul_neg, neg_sub]

theorem Gr.eq_of_pr {g h : A} (hg : Gr a g) (hh : Gr a h) (h1 : ‖1 - a g‖ ≤ 1 / 2) (h2 : ‖1 - a h‖ ≤ 1 / 2)
    (e : pr a g = pr a h) : g = h := by
  have e1 : g - a g = h - a h := by
    have := congrArg (fun x => (2 : ℝ) • x) e
    simpa [pr_apply, smul_smul] using this
  set D := g - h with hD
  have e2 : a g * D * a h = -D := by
    rw [hD, mul_sub, sub_mul, hg.1, one_mul, mul_assoc, hh.2, mul_one]
    have : a h = h - (g - a g) := by rw [e1]; abel
    rw [this]; abel
  have e3 : (2 : ℝ) • D = (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) := by
    have : (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) = D - a g * D * a h := by noncomm_ring
    rw [this, e2, two_smul, sub_neg_eq_add]
  have n1 : ‖(1 - a g) * D‖ ≤ 1 / 2 * ‖D‖ := (norm_mul_le _ _).trans (by gcongr)
  have n2 : ‖D * (1 - a h)‖ ≤ ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n3 : ‖(1 - a g) * D * (1 - a h)‖ ≤ 1 / 2 * ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n4 : 2 * ‖D‖ ≤ ‖(1 - a g) * D‖ + ‖D * (1 - a h)‖ + ‖(1 - a g) * D * (1 - a h)‖ := by
    have : ‖(2 : ℝ) • D‖ = 2 * ‖D‖ := by rw [norm_smul]; norm_num
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖D‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem prod_strict : ∀ (m : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : Fin m → V → A)
    (e' : Fin m → V →L[ℝ] A) (_ : ∀ i, HasStrictFDerivAt (e i) (e' i) 0) (_ : ∀ i, e i 0 = 1),
    HasStrictFDerivAt (fun s => (List.ofFn fun i => e i s).prod) (∑ i, e' i) 0 := by
  intro m V _ _
  induction m with
  | zero =>
    intro e e' _ _
    simpa using hasStrictFDerivAt_const (1 : A) (0 : V)
  | succ m ih =>
    intro e e' he h0
    have h1 := (he 0).mul' (ih (fun i => e i.succ) (fun i => e' i.succ) (fun i => he _) (fun i => h0 _))
    have h2 : (List.ofFn fun i : Fin m => e i.succ 0).prod = 1 := by simp [h0]
    simp only [h2] at h1
    simp only [h0, one_smul, MulOpposite.op_one] at h1
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    rw [add_comm (e' 0)]
    exact h1

theorem coords (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {m : ℕ} (Y : Fin m → A) (hY : ∀ i, a (Y i) = -Y i)
    (c : A →L[ℝ] (Fin m → ℝ)) (hc : ∀ s : Fin m → ℝ, c (∑ i, s i • Y i) = s)
    (hc' : ∀ x y, a x = -x → a y = -y → c x = c y → x = y)
    (e : Fin m → ℝ → A) (he : ∀ i, HasStrictDerivAt (e i) (Y i) 0) (he0 : ∀ i, e i 0 = 1) (heG : ∀ i t, Gr a (e i t))
    (g : ℝ → A) (Z : A) (hg : HasDerivAt g Z 0) (hg0 : g 0 = 1) (hgG : ∀ t, Gr a (g t)) :
    ∃ s : ℝ → Fin m → ℝ, s 0 = 0 ∧ HasDerivAt s (c (pr a Z)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), g t = (List.ofFn fun i => e i (s t i)).prod := by
  set Φ : (Fin m → ℝ) → A := fun s => (List.ofFn fun i => e i (s i)).prod with hΦ
  have hΦ0 : Φ 0 = 1 := by simp [hΦ, he0]
  have hΦG : ∀ s, Gr a (Φ s) := fun s => Gr.list ha h1 _ fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact heG _ _
  have hΦd : HasStrictFDerivAt Φ
      (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp (ContinuousLinearMap.proj i)) 0 :=
    prod_strict m (fun i (s : Fin m → ℝ) => e i (s i)) _ (fun i =>
      HasStrictFDerivAt.comp (0 : Fin m → ℝ) (f := fun s : Fin m → ℝ => s i) (he i).hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasStrictFDerivAt) he0
  have hΨ : HasStrictFDerivAt (fun s => c (pr a (Φ s)))
      ((ContinuousLinearEquiv.refl ℝ (Fin m → ℝ) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) 0 := by
    have h2 := (c.comp (pr a)).hasStrictFDerivAt.comp 0 hΦd
    refine HasStrictFDerivAt.congr_fderiv h2 (ContinuousLinearMap.ext fun s => ?_)
    have h3 : pr a (∑ i, s i • Y i) = ∑ i, s i • Y i := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, pr_apply, hY, sub_neg_eq_add, ← two_smul ℝ (Y i), smul_smul (1 / 2 : ℝ)]
      norm_num
    have h4 : (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s = ∑ i, s i • Y i := by
      rw [sum_apply]
      rfl
    change c (pr a ((∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s)) = s
    rw [h4, h3, hc]
  set ρ := hΨ.localInverse _ _ _ with hρ
  have hz : c (pr a (Φ 0)) = c (pr a (g 0)) := by rw [hΦ0, hg0]
  have hk : HasDerivAt (fun t => c (pr a (g t))) (c (pr a Z)) 0 :=
    (c.comp (pr a)).hasFDerivAt.comp_hasDerivAt 0 hg
  have hρ0 : ρ (c (pr a (g 0))) = 0 := by
    rw [← hz]
    exact hΨ.localInverse_apply_image
  have hρd := hΨ.to_localInverse.hasFDerivAt
  rw [hz] at hρd
  have hs : HasDerivAt (fun t => ρ (c (pr a (g t)))) (c (pr a Z)) 0 := by
    have h5 := hρd.comp_hasDerivAt 0 hk
    exact h5
  refine ⟨fun t => ρ (c (pr a (g t))), hρ0, hs, ?_⟩
  have hr := hΨ.eventually_right_inverse
  rw [hz] at hr
  have near : ∀ k : ℝ → A, ContinuousAt k 0 → k 0 = 1 → ∀ᶠ t in 𝓝 (0 : ℝ), ‖1 - a (k t)‖ ≤ 1 / 2 := fun k hk hk0 => by
    have h4 : ContinuousAt (fun t => ‖1 - a (k t)‖) 0 :=
      (continuousAt_const.sub (a.continuous.continuousAt.comp hk)).norm
    have h5 := h4.tendsto
    simp only [hk0, h1, sub_self, norm_zero] at h5
    exact h5.eventually (eventually_le_nhds (by norm_num))
  have hΦc : ContinuousAt (fun t => Φ (ρ (c (pr a (g t))))) 0 :=
    ContinuousAt.comp_of_eq (g := Φ) (f := fun t => ρ (c (pr a (g t)))) hΦd.continuousAt hs.continuousAt hρ0
  filter_upwards [hk.continuousAt.tendsto hr, near g hg.continuousAt hg0,
    near _ hΦc (by simp only [hρ0, hΦ0])] with t t1 t2 t3
  exact (hgG t).eq_of_pr (hΦG _) t2 t3
    (hc' _ _ ((hgG t).anti ha h1) ((hΦG _).anti ha h1) (Eq.symm t1))

theorem gr_exp [CompleteSpace A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {Y : A} (hY : a Y = -Y) :
    Gr a (NormedSpace.exp Y) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let φ : A →+* Aᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (a x)
      map_one' := by rw [h1]; rfl
      map_mul' := fun x y => by rw [ha]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add]; rfl }
  have h2 := NormedSpace.map_exp φ (MulOpposite.continuous_op.comp a.continuous) Y
  have h3 : a (NormedSpace.exp Y) = NormedSpace.exp (-Y) := by
    apply MulOpposite.op_injective
    rw [← hY, ← NormedSpace.exp_op]
    exact h2
  constructor
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem main [FiniteDimensional ℝ A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) :
    ∃ (m : ℕ) (Y : Fin m → A) (c : Fin m → A →ₗ[ℝ] ℝ), (∀ i, a (Y i) = -Y i) ∧ ∀ Z : A,
      (∀ t : ℝ, Gr a (NormedSpace.exp (t • Z))) → ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), NormedSpace.exp (t • Z) = (List.ofFn fun i => NormedSpace.exp (s i t • Y i)).prod := by
  have : CompleteSpace A := FiniteDimensional.complete ℝ A
  let L : Submodule ℝ A := LinearMap.ker ((a : A →ₗ[ℝ] A) + LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ a x = -x := fun x => by
    simp [L, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ L
  obtain ⟨q, hq⟩ := L.subtype.exists_leftInverse_of_injective L.ker_subtype
  have hq' : ∀ x : L, q x = x := fun x => LinearMap.congr_fun hq x
  let c : A →L[ℝ] (Fin (Module.finrank ℝ L) → ℝ) := LinearMap.toContinuousLinearMap (b.equivFun.toLinearMap ∘ₗ q)
  have hc0 : ∀ x : L, c x = b.equivFun x := fun x => by
    change b.equivFun (q x) = _
    rw [hq']
  refine ⟨_, fun i => b i, fun i => (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp (c.comp (pr a)).toLinearMap,
    fun i => (hL _).1 (b i).2, fun Z hZ => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := coords ha h1 (fun i => (b i : A)) (fun i => (hL _).1 (b i).2) c
    (fun s => by
      have : (∑ i, s i • (b i : A)) = ((b.equivFun.symm s : L) : A) := by simp [Module.Basis.equivFun_symm_apply]
      rw [this, hc0, LinearEquiv.apply_symm_apply])
    (fun x y hx hy e => by
      have e1 := (hc0 ⟨x, (hL x).2 hx⟩).symm.trans (e.trans (hc0 ⟨y, (hL y).2 hy⟩))
      exact congrArg Subtype.val (b.equivFun.injective e1))
    (fun i t => NormedSpace.exp (t • (b i : A)))
    (fun i => by simpa using hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (b i : A) (0 : ℝ))
    (fun i => by simp)
    (fun i t => gr_exp ha h1 (by rw [map_smul, (hL _).1 (b i).2, smul_neg]))
    (fun t => NormedSpace.exp (t • Z)) Z
    (by simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)) (by simp) hZ
  exact ⟨fun i t => s t i, fun i => congrFun s0 i, fun i => hasDerivAt_pi.1 sd i, se⟩

end Alg

end PositivityTheory.ThKEst.LinDerPf

end
