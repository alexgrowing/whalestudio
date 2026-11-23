import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibFour

noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  refine ⟨h₁.1.sub h₂.1, h₁.2.1.sub h₂.2.1, fun S hS => ?_⟩
  rw [integral_sub h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_sub (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  refine ⟨h.1.const_mul c, continuous_const.mul h.2.1, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, h.2.2 S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  rw [not_le] at hneg
  have hev : ∀ᶠ b in 𝓝 b0, D b < D b0 / 2 :=
    hD.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds hev
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hpos' : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
  have hge := setIntegral_ge_of_const_le_real (c := -(D b0 / 2)) (f := fun b => -D b) hSm hlt
    (fun b hb => by
      have : D b < D b0 / 2 := hSsub hb
      linarith)
    (hD.neg.continuousOn.integrableOn_compact hSc)
  rw [integral_neg] at hge
  have := h0 S hSc
  nlinarith

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have := nonneg_of_setIntegral (ν := ν) _ h.2.1 (fun S hS => by
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.2 (hle v)) b
  linarith

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  rw [AddSubgroup.coe_inf]
  refine h₀o.inter ?_
  simp only [AddSubgroup.coe_iInf]
  exact isOpen_biInter_finset fun i _ => hLo i

theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hN : ∀ x : V, {z : V | |φ (x + z) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
    intro x
    have hcx : Continuous fun z : V => |φ (x + z) - φ x| :=
      ((hc.comp (continuous_const.add continuous_id)).sub continuous_const).abs
    have : IsOpen {z : V | |φ (x + z) - φ x| < ε / 2} := isOpen_lt hcx continuous_const
    exact this.mem_nhds (by simp; linarith)
  choose L hLo hLc hLN using fun x => hNA _ (hN x)
  have hcov : tsupport φ ⊆ ⋃ x : tsupport φ, {y : V | y - (x : V) ∈ L x} := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(L y).zero_mem]⟩
  have hopen : ∀ x : tsupport φ, IsOpen {y : V | y - (x : V) ∈ L x} := fun x =>
    (hLo x).preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover _ hopen hcov
  have ho := isOpen_inf_iInf Λ₀ h₀o t (fun x : tsupport φ => L (x : V)) (fun x => hLo _)
  refine ⟨Λ₀ ⊓ ⨅ x ∈ t, L (x : V), ho, ?_, inf_le_left, ?_⟩
  · exact h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ ho)
      (by rw [AddSubgroup.coe_inf]; exact inter_subset_left)
  · intro x z hz
    have hz' : ∀ i ∈ t, z ∈ L (i : V) := by
      intro i hi
      have := (inf_le_right : Λ₀ ⊓ ⨅ x ∈ t, L (x : V) ≤ _) hz
      exact (AddSubgroup.mem_iInf.1 this i |> AddSubgroup.mem_iInf.1) hi
    have key : ∀ i ∈ t, x - (i : V) ∈ L (i : V) → |φ (x + z) - φ x| < ε := by
      intro i hi hxi
      have h1 := hLN (i : V) hxi
      have h2 := hLN (i : V) (show x + z - (i : V) ∈ L (i : V) by
        have := (L (i : V)).add_mem hxi (hz' i hi)
        rwa [show x - (i : V) + z = x + z - (i : V) by abel] at this)
      simp only [mem_setOf_eq, add_sub_cancel] at h1 h2
      calc |φ (x + z) - φ x| ≤ |φ (x + z) - φ i| + |φ x - φ i| := by
            rw [abs_sub_comm (φ x)]; exact abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add h2 h1
        _ = ε := by ring
    by_cases hx : x ∈ tsupport φ
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact key i hi hxi
    · by_cases hxz : x + z ∈ tsupport φ
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hxz)
        refine key i hi ?_
        have := (L (i : V)).sub_mem hxi (hz' i hi)
        rwa [show x + z - (i : V) - z = x - (i : V) by abel] at this
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]
        simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ :=
  QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ))

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x :=
  congrArg (fun q : V ⧸ Λ => φ q.out) (QuotientAddGroup.eq.2 h).symm

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | -x + y ∈ Λ}, hΛ.preimage (continuous_const.add continuous_id), ?_,
    fun y hy => cosApx_eq Λ φ hy⟩
  show -x + x ∈ Λ
  rw [neg_add_cancel]
  exact Λ.zero_mem

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  intro hLC φ hφ
  obtain ⟨hc, hs, hsU⟩ := hφ
  obtain ⟨W, hW, hKW⟩ := compact_open_separated_add_right hs.isCompact hU hsU
  obtain ⟨Λ₀, h₀o, h₀c, h₀W⟩ := hNA W hW
  set K' : Set V := tsupport φ + (Λ₀ : Set V) with hK'
  have hcos : ∀ x y, -x + y ∈ Λ₀ → y ∈ K' → x ∈ K' := by
    intro x y h hy
    obtain ⟨k, hk, l, hl, rfl⟩ := hy
    exact ⟨k, hk, l - (-x + (k + l)), Λ₀.sub_mem hl h, by abel⟩
  have hcos' : ∀ x y, -x + y ∈ Λ₀ → (y ∈ K' ↔ x ∈ K') := by
    intro x y h
    refine ⟨hcos x y h, hcos y x ?_⟩
    have := Λ₀.neg_mem h
    rwa [neg_add_rev, neg_neg] at this
  have hnb : ∀ x : V, {y | -x + y ∈ Λ₀} ∈ 𝓝 x := by
    intro x
    refine (h₀o.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    show -x + x ∈ Λ₀
    rw [neg_add_cancel]
    exact Λ₀.zero_mem
  have hK'cl : IsClosed K' := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.mem_of_superset (hnb x) fun y hy hyK => hx (hcos x y hy hyK)
  have hK'c : IsCompact K' := hs.isCompact.add h₀c
  have hK'U : K' ⊆ U := (Set.add_subset_add subset_rfl h₀W).trans hKW
  have hKK' : tsupport φ ⊆ K' := fun x hx => ⟨x, hx, 0, Λ₀.zero_mem, add_zero x⟩
  have hlcc : ∀ ψ : V → ℝ, IsLocallyConstant ψ → Function.support ψ ⊆ K' → IsLCcOn U ψ :=
    fun ψ h1 h2 => ⟨h1, hK'c.of_isClosed_subset isClosed_closure (closure_minimal h2 hK'cl),
      (closure_minimal h2 hK'cl).trans hK'U⟩
  have hdens : ∀ ψ, IsLCcOn U ψ → ∃ g, HasDens μ f ι ν ψ g := fun ψ h => by
    obtain ⟨g, hg, hS⟩ := hLC ψ h
    exact ⟨g, h.1.continuous.integrable_of_hasCompactSupport h.2.1, hg, hS⟩
  set ind : V → ℝ := K'.indicator fun _ => 1 with hind_def
  have hind : IsLCcOn U ind := by
    refine hlcc ind ?_ Set.support_indicator_subset
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | -x + y ∈ Λ₀}, h₀o.preimage (continuous_const.add continuous_id),
      mem_of_mem_nhds (hnb x), fun y hy => ?_⟩
    have := hcos' x y hy
    rw [hind_def]
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx (this.1 h)]
  obtain ⟨g0, hg0⟩ := hdens ind hind
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose Λ hΛo hΛc hΛ0 hosc using fun n : ℕ => exists_sub_osc hNA hc hs (hε n) Λ₀ h₀o h₀c
  set φn : ℕ → V → ℝ := fun n => cosApx (Λ n) φ with hφn_def
  have hφn_close : ∀ n x, |φn n x - φ x| < 1 / ((n : ℝ) + 1) := by
    intro n x
    have := hosc n ((x : V ⧸ Λ n).out) _ (cosApx_sub_mem (Λ n) x)
    rw [add_neg_cancel_left] at this
    rw [abs_sub_comm]
    exact this
  have hφn_supp : ∀ n, Function.support (φn n) ⊆ K' := by
    intro n x hx
    exact ⟨_, subset_tsupport φ hx, _, hΛ0 n (cosApx_sub_mem (Λ n) x), add_neg_cancel_left _ x⟩
  have hφn : ∀ n, IsLCcOn U (φn n) := fun n => hlcc _ (cosApx_lc _ (hΛo n) φ) (hφn_supp n)
  choose g hg using fun n => hdens (φn n) (hφn n)
  have hbd : ∀ n x, |φn n x - φ x| ≤ 1 / ((n : ℝ) + 1) * ind x := by
    intro n x
    by_cases hx : x ∈ K'
    · rw [hind_def, Set.indicator_of_mem hx, mul_one]
      exact (hφn_close n x).le
    · have h1 : φn n x = 0 := by
        by_contra h
        exact hx (hφn_supp n h)
      have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hKK' h)
      rw [hind_def, Set.indicator_of_notMem hx, h1, h2]
      simp
  have hgg : ∀ n m b, |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := by
    intro n m b
    have hA := hg0.const_mul (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))
    have hle : ∀ n m x, φn n x - φn m x ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * ind x := by
      intro n m x
      have h1 := abs_le.1 (hbd n x)
      have h2 := abs_le.1 (hbd m x)
      rw [add_mul]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have u1 := ((hg n).sub (hg m)).le hA (hle n m) b
    have hA' := hg0.const_mul (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))
    have u2 := ((hg m).sub (hg n)).le hA' (hle m n) b
    refine abs_le.2 ⟨?_, u1⟩
    have : (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) :=
      add_comm _ _
    rw [this] at u2
    linarith
  have hcauchy : ∀ b, CauchySeq fun n => g n b := by
    intro b
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)) * |g0 b|)
      (fun n m N hn hm => ?_) ?_
    · rw [Real.dist_eq]
      have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hM : (N : ℝ) ≤ m := by exact_mod_cast hm
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      calc |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := hgg n m b
        _ ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * (1 / ((N : ℝ) + 1)) * |g0 b| := by ring
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const |g0 b|
      rwa [mul_zero, zero_mul] at this
  set G : X → ℝ := fun b => limUnder atTop fun n => g n b with hG_def
  have hlim : ∀ b, Tendsto (fun n => g n b) atTop (𝓝 (G b)) := fun b =>
    (hcauchy b).tendsto_limUnder
  have hGn : ∀ n b, |G b - g n b| ≤ 1 / ((n : ℝ) + 1) * g0 b := by
    intro n b
    have ht : Tendsto (fun m => |g m b - g n b|) atTop (𝓝 |G b - g n b|) :=
      ((hlim b).sub_const _).abs
    have ht2 : Tendsto (fun m : ℕ => (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b) atTop
        (𝓝 ((1 / ((n : ℝ) + 1) + 0) * g0 b)) :=
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _
    have := le_of_tendsto_of_tendsto' ht ht2 fun m => by
      rw [abs_sub_comm]
      exact hgg n m b
    rwa [add_zero] at this
  have hGc : Continuous G := by
    refine TendstoLocallyUniformly.continuous (F := g) (p := atTop) ?_
      (Eventually.of_forall fun n => (hg n).2.1).frequently
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hεp x
    refine ⟨{y | g0 y < g0 x + 1}, (isOpen_lt hg0.2.1 continuous_const).mem_nhds (by simp), ?_⟩
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (|g0 x| + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (|g0 x| + 1)
      rwa [zero_mul] at this
    filter_upwards [ht.eventually (Iio_mem_nhds hεp)] with n hn y hy
    have hy' : g0 y < g0 x + 1 := hy
    have hx' := le_abs_self (g0 x)
    rw [Real.dist_eq]
    calc |G y - g n y| ≤ 1 / ((n : ℝ) + 1) * g0 y := hGn n y
      _ ≤ 1 / ((n : ℝ) + 1) * (|g0 x| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < ε := hn
  refine ⟨G, hGc, fun S hS => ?_⟩
  have hφi : Integrable φ μ := hc.integrable_of_hasCompactSupport hs
  have hC : ∀ n : ℕ, |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| ≤
      2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν| := by
    intro n
    have e1 : |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ v in f ⁻¹' (ι '' S), φn n v ∂μ| ≤
        ∫ v in f ⁻¹' (ι '' S), 1 / ((n : ℝ) + 1) * ind v ∂μ := by
      rw [← integral_sub hφi.integrableOn (hg n).1.integrableOn, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun v => 1 / ((n : ℝ) + 1) * ind v)
        (hg0.1.const_mul _).integrableOn (ae_of_all _ ?_)
      intro x
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbd n x
    have e2 : |∫ b in S, g n b ∂ν - ∫ b in S, G b ∂ν| ≤ ∫ b in S, 1 / ((n : ℝ) + 1) * g0 b ∂ν := by
      rw [← integral_sub ((hg n).2.1.continuousOn.integrableOn_compact hS)
        (hGc.continuousOn.integrableOn_compact hS), ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun b => 1 / ((n : ℝ) + 1) * g0 b)
        ((continuous_const.mul hg0.2.1).continuousOn.integrableOn_compact hS) (ae_of_all _ ?_)
      intro b
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hGn n b
    rw [integral_const_mul, hg0.2.2 S hS] at e1
    rw [integral_const_mul] at e2
    rw [(hg n).2.2 S hS] at e1
    have h3 := abs_sub_le (∫ v in f ⁻¹' (ι '' S), φ v ∂μ) (∫ b in S, g n b ∂ν) (∫ b in S, G b ∂ν)
    have h4 : 1 / ((n : ℝ) + 1) * ∫ b in S, g0 b ∂ν ≤ 1 / ((n : ℝ) + 1) * |∫ b in S, g0 b ∂ν| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    linarith
  by_contra hne
  have hpos : 0 < |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  have ht : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν|) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const
      |∫ b in S, g0 b ∂ν|
    rwa [mul_zero, zero_mul] at this
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hpos)).exists
  exact absurd (hC n) (not_le.2 hn)

end Main

end PI.VolStabW
