import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace EuclideanSections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') : IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem eventually_shift_le (D m : ℕ) (b E δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n ≤ N → N ≤ n + m →
      b * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) + E * ((N : ℝ) + 1) ^ D ≤
        (b + δ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF0 : 0 < F := by positivity
  have hlin : ∀ c : ℝ, (fun n : ℕ => (n : ℝ) + c) ~[atTop] fun n : ℕ => (n : ℝ) := fun c =>
    IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop c).comp_tendsto tendsto_natCast_atTop_atTop)
  have hu : (fun n : ℕ => ((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := (hlin m).pow (D + 1)
  have hv : (fun n : ℕ => ((n : ℝ) + (m + 1)) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    ((hlin (m + 1)).pow D).isBigO.trans_isLittleO
      ((isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop)
  set c₁ := δ / (2 * (|b| + 1)) with hc₁
  set c₂ := δ / (2 * F * (|E| + 1)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  have hbc : |b| * c₁ ≤ δ / 2 := by
    rw [hc₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg b]
  have hEc : F * (|E| * c₂) ≤ δ / 2 := by
    rw [hc₂, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg E]
  filter_upwards [hu.def hc₁0, hv.def hc₂0] with n h1 h2
  intro N hnN hNn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hN1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN2 : (N : ℝ) ≤ n + m := by exact_mod_cast hNn
  have hw : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
  have hpow : (N : ℝ) ^ (D + 1) ≤ ((n : ℝ) + m) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hN2 _
  have hpow' : (n : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (D + 1) := pow_le_pow_left₀ hn0 hN1 _
  have hv' : ((N : ℝ) + 1) ^ D ≤ ((n : ℝ) + (m + 1)) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by linarith)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by positivity)] at h2
  have hb : b * (N : ℝ) ^ (D + 1) ≤
      b * (n : ℝ) ^ (D + 1) + |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · nlinarith [abs_nonneg b, mul_le_mul_of_nonpos_left hpow' hb]
  have hE : E * ((N : ℝ) + 1) ^ D ≤ |E| * ((n : ℝ) + (m + 1)) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hv' (abs_nonneg E))
  have hb2 : |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) ≤ δ / 2 * (n : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg b)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbc hw)
  have hE2 : |E| * F * ((n : ℝ) + (m + 1)) ^ D ≤ δ / 2 * (n : ℝ) ^ (D + 1) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg E) hF0.le)
    nlinarith [mul_le_mul_of_nonneg_right hEc hw]
  have key : b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D) ≤ (b + δ) * (n : ℝ) ^ (D + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hE hF0.le]
  rw [show b * ((N : ℝ) ^ (D + 1) / F) + E * ((N : ℝ) + 1) ^ D =
      (b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D)) / F by field_simp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hF0.le

end EuclideanSections

open EuclideanSections in

theorem EuclideanSections.proof (hP : EuclideanSectionsPower.Statement) (hS : SmallSectionsNonzero.Statement)
    (hL : SublatticeDegree.Statement) (hG : SuccessiveMinimaSpan.Statement) : EuclideanSections.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hconj
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hcon, ⟨Cr, hr⟩, m, hm, hdeg⟩ :=
    hP K ι Ω y D A P0 II hD hII har hb hA hconj
  obtain ⟨C, hC⟩ := hG K ι Ω y D A P0 hD har hb hA
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, ⟨Cr, hr⟩, fun ε hε => ?_⟩
  set C₁ := max C 1 with hC₁
  have hC₁1 : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hlog : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁1
  set I := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hI
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdeg (ε / 2) (half_pos hε))
  filter_upwards [eventually_shift_le D m (I + ε / 2) (Cr * Real.log C₁) (ε / 2) (half_pos hε),
    eventually_ge_atTop (m * Q)] with n hn hnQ
  intro _ _
  have hqQ : Q ≤ n / m + 1 := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hnQ))
  have hnN : n ≤ m * (n / m + 1) := (Nat.lt_mul_div_succ n hm).le
  have hNn : m * (n / m + 1) ≤ n + m := by
    have := Nat.mul_div_le n m
    rw [mul_add, mul_one]
    omega
  suffices main : ∀ N : ℕ, n ≤ N → N ≤ n + m →
      -Real.log (ZLattice.covolume (imageLattice (φ N))) ≤
        (I + ε / 2) * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) →
      -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
        (I + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) from
    main _ hnN hNn (hQ (n / m + 1) hqQ)
  intro N hnN hNn h1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnN
  obtain ⟨t, ht, ht0, hts⟩ := hS K ι Ω y D A P0 har hb hA j

  let ψ : chartLat y A.a n →+ chartLat y A.a (n + j) :=
    { toFun := fun s => ⟨(s : Ω) * t, mul_mem_chartLat s.2 ht⟩
      map_zero' := by ext; simp
      map_add' := fun s s' => by ext; simp [add_mul] }
  have hψ : Function.Injective ψ := fun s s' h =>
    Subtype.ext (mul_right_cancel₀ ht0 (congrArg Subtype.val h))
  have hψn : ∀ s, ‖φ (n + j) (ψ s)‖ ≤ ‖φ n s‖ := fun s => hcon n j s ⟨t, ht⟩ (ψ s) hts rfl

  have hclos : AddSubgroup.closure
      {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have hx : (x : Ω) ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s} := by
      rw [hC (n + j)]; exact x.2
    have key : ∀ z (hz : z ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s}),
        ∃ hz' : z ∈ chartLat y A.a (n + j), (⟨z, hz'⟩ : chartLat y A.a (n + j)) ∈ AddSubgroup.closure
          {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz => exact ⟨hz.1, AddSubgroup.subset_closure (isBoundedH_mono hz.2 (le_max_left _ _))⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add z w _ _ hz hw =>
        obtain ⟨hz', hz''⟩ := hz
        obtain ⟨hw', hw''⟩ := hw
        exact ⟨add_mem hz' hw', add_mem hz'' hw''⟩
      | neg z _ hz =>
        obtain ⟨hz', hz''⟩ := hz
        exact ⟨neg_mem hz', neg_mem hz''⟩
    obtain ⟨_, hx'⟩ := key x hx
    exact hx'
  have hbound : ∀ s ∈ {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)},
      ‖φ (n + j) s‖ ≤ C₁ := fun s hs => hsup (n + j) C₁ s (by linarith) hs
  have h2 := hL (chartLat y A.a (n + j)) (chartLat y A.a n) (r (n + j)) (r n) (φ (n + j)) (φ n) ψ _ C₁
    (hinj _) (hinj _) hψ hψn hclos hbound hC₁1
  have h3 : (r (n + j) : ℝ) * Real.log C₁ ≤ Cr * Real.log C₁ * (((n + j : ℕ) : ℝ) + 1) ^ D := by
    have := mul_le_mul_of_nonneg_right (hr (n + j)) hlog
    linarith
  have h4 := hn (n + j) (Nat.le_add_right n j) hNn
  have h5 : I + ε / 2 + ε / 2 = I + ε := by ring
  rw [h5] at h4
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
