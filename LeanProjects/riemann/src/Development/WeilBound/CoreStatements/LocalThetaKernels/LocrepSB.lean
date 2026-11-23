import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace PositivityTheory.ThKH.Locrep

open Filter Topology GlobalTheory.WeilM

variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)

def put (x : A) (y : K) : A := x - ι (ev x) + ι y

def Pm (φ : K → ℂ) (y : K) : Module.End ℂ (A → ℂ) where
  toFun Φ x := φ (ev x) * Φ (put ev ι x y)
  map_add' Φ Ψ := by funext x; simp [mul_add]
  map_smul' c Φ := by funext x; simp [mul_left_comm]

theorem Pm_apply (φ : K → ℂ) (y : K) (Φ : A → ℂ) (x : A) : Pm ev ι φ y Φ x = φ (ev x) * Φ (put ev ι x y) := rfl

theorem put_self (x : A) : put ev ι x (ev x) = x := by
  simp [put]

variable {ev ι}

theorem ev_put (h : ∀ y, ev (ι y) = y) (x : A) (y : K) : ev (put ev ι x y) = y := by
  simp [put, h]

theorem put_put (h : ∀ y, ev (ι y) = y) (x : A) (y z : K) : put ev ι (put ev ι x y) z = put ev ι x z := by
  simp only [put, map_add, map_sub, h, sub_self, zero_add]
  abel

theorem Pm_Pm (h : ∀ y, ev (ι y) = y) (φ φ₁ : K → ℂ) (a y : K) (Φ : A → ℂ) :
    Pm ev ι φ a (Pm ev ι φ₁ y Φ) = φ₁ a • Pm ev ι φ y Φ := by
  funext x
  simp only [Pm_apply, ev_put h, put_put h, Pi.smul_apply, smul_eq_mul]
  ring

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]

omit [IsTopologicalAddGroup K] in
theorem continuous_put (hev : Continuous ev) (hι : Continuous ι) : Continuous fun p : A × K => put ev ι p.1 p.2 := by
  show Continuous fun p : A × K => p.1 - ι (ev p.1) + ι p.2
  exact (continuous_fst.sub (hι.comp (hev.comp continuous_fst))).add (hι.comp continuous_snd)

omit [IsTopologicalAddGroup K] in
theorem Pm_mem_SB (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {φ : K → ℂ} (hφ : φ ∈ SB K) (y : K)
    {g : A → ℂ} (hg : g ∈ SB A) : Pm ev ι φ y g ∈ SB A := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hput : Continuous fun x : A => put ev ι x y :=
    (continuous_id.sub (hι.comp hev)).add continuous_const
  have hfun : (Pm ev ι φ y g : A → ℂ) = fun x => φ (ev x) * g (put ev ι x y) :=
    funext (Pm_apply ev ι φ y g)
  show IsLocallyConstant (Pm ev ι φ y g) ∧ HasCompactSupport (Pm ev ι φ y g)
  rw [hfun]
  refine ⟨(hφ'.1.comp_continuous hev).mul (hg'.1.comp_continuous hput), ?_⟩
  have hc : Continuous fun p : A × K => p.1 + ι p.2 - ι y :=
    (continuous_fst.add (hι.comp continuous_snd)).sub continuous_const
  have hK : IsCompact ((fun p : A × K => p.1 + ι p.2 - ι y) '' (tsupport g ×ˢ tsupport φ)) :=
    (hg'.2.prod hφ'.2).image hc
  have hsub : Function.support (fun x => φ (ev x) * g (put ev ι x y)) ⊆
      (fun p : A × K => p.1 + ι p.2 - ι y) '' (tsupport g ×ˢ tsupport φ) := by
    intro x hx
    have hx' : φ (ev x) * g (put ev ι x y) ≠ 0 := hx
    have h1 : φ (ev x) ≠ 0 := left_ne_zero_of_mul hx'
    have h2 : g (put ev ι x y) ≠ 0 := right_ne_zero_of_mul hx'
    refine ⟨(put ev ι x y, ev x), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, ?_⟩
    simp only [put]
    abel
  exact IsCompact.of_isClosed_subset hK.closure isClosed_closure (closure_mono hsub)

theorem mem_span_Pm (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {g : A → ℂ} (hg : g ∈ SB A) :
    g ∈ Submodule.span ℂ {f | ∃ φ ∈ SB K, ∃ y, f = Pm ev ι φ y g} := by
  classical
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hπc : Continuous fun z : A => z - ι (ev z) := continuous_id.sub (hι.comp hev)
  have hKa : IsCompact ((fun z : A => z - ι (ev z)) '' tsupport g) := hg'.2.image hπc
  have hC : IsCompact (ev '' tsupport g) := hg'.2.image hev
  have hput_eq : ∀ x k, put ev ι x k = (x - ι (ev x)) + ι k := fun x k => rfl
  have hout : ∀ a k, ev a = 0 → a ∉ (fun z : A => z - ι (ev z)) '' tsupport g → g (a + ι k) = 0 := by
    intro a k ha hnot
    by_contra hne
    apply hnot
    refine ⟨a + ι k, subset_tsupport _ hne, ?_⟩
    simp [ha, h]
  have htube : ∀ k0 : K, ∀ᶠ k in 𝓝 k0, ∀ a ∈ (fun z : A => z - ι (ev z)) '' tsupport g,
      g (a + ι k) = g (a + ι k0) := by
    intro k0
    apply hKa.eventually_forall_of_forall_eventually
    intro a _
    have h1 : ∀ᶠ p in 𝓝 (k0, a), g (p.2 + ι p.1) = g (a + ι k0) :=
      ((continuous_snd.add (hι.comp continuous_fst)).tendsto (k0, a)).eventually
        (hg'.1.eventually_eq (a + ι k0))
    have h2 : ∀ᶠ p in 𝓝 (k0, a), g (p.2 + ι k0) = g (a + ι k0) :=
      ((continuous_snd.add continuous_const).tendsto (k0, a)).eventually
        (hg'.1.eventually_eq (a + ι k0))
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2]
  let F : K → A → ℂ := fun k x => g (put ev ι x k)
  have hFloc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k0
    filter_upwards [htube k0] with k hk
    funext x
    show g (put ev ι x k) = g (put ev ι x k0)
    rw [hput_eq, hput_eq]
    have hev0 : ev (x - ι (ev x)) = 0 := by simp [h]
    by_cases hx : x - ι (ev x) ∈ (fun z : A => z - ι (ev z)) '' tsupport g
    · exact hk _ hx
    · rw [hout _ _ hev0 hx, hout _ _ hev0 hx]
  have hFzero : ∀ k, k ∉ ev '' tsupport g → F k = 0 := by
    intro k hk
    funext x
    by_contra hne
    apply hk
    exact ⟨put ev ι x k, subset_tsupport _ hne, ev_put h x k⟩
  have hfin : (F '' (ev '' tsupport g)).Finite := by
    letI : TopologicalSpace (A → ℂ) := ⊥
    haveI : DiscreteTopology (A → ℂ) := ⟨rfl⟩
    exact (hC.image hFloc.continuous).finite_of_discrete
  let Vs : Finset (A → ℂ) := hfin.toFinset.filter (· ≠ 0)
  let rep : (A → ℂ) → K := fun v => if hv : ∃ k, F k = v then hv.choose else 0
  let φv : (A → ℂ) → K → ℂ := fun v k => if F k = v then 1 else 0
  have hrep : ∀ v ∈ Vs, F (rep v) = v := by
    intro v hv
    have hv' := (Finset.mem_filter.1 hv).1
    rw [Set.Finite.mem_toFinset] at hv'
    obtain ⟨k, _, hk⟩ := hv'
    have hex : ∃ k, F k = v := ⟨k, hk⟩
    show F (if hv : ∃ k, F k = v then hv.choose else 0) = v
    rw [dif_pos hex]
    exact hex.choose_spec
  have hφv : ∀ v ∈ Vs, φv v ∈ SB K := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_filter.1 hv).2
    refine ⟨hFloc.comp (fun w : A → ℂ => if w = v then (1 : ℂ) else 0), ?_⟩
    have hsupp : Function.support (φv v) ⊆ {k | F k = v} := by
      intro k hk
      by_contra hne
      exact hk (if_neg hne)
    have hL : {k | F k = v} ⊆ ev '' tsupport g := by
      intro k hk
      by_contra hc
      exact hv0 (hk.symm.trans (hFzero k hc))
    exact IsCompact.of_isClosed_subset hC (isClosed_tsupport _)
      ((closure_minimal hsupp (hFloc.isClosed_fiber v)).trans hL)
  have hsum : g = ∑ v ∈ Vs, Pm ev ι (φv v) (rep v) g := by
    funext x
    rw [Finset.sum_apply]
    have hterm : ∀ v ∈ Vs, Pm ev ι (φv v) (rep v) g x = if F (ev x) = v then v x else 0 := by
      intro v hv
      rw [Pm_apply]
      have hx : g (put ev ι x (rep v)) = v x := congrFun (hrep v hv) x
      rw [hx]
      show (if F (ev x) = v then (1 : ℂ) else 0) * v x = _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    have hgx : g x = F (ev x) x := by
      show g x = g (put ev ι x (ev x))
      rw [put_self]
    by_cases hmem : F (ev x) ∈ Vs
    · rw [if_pos hmem, ← hgx]
    · rw [if_neg hmem]
      have h0 : F (ev x) = 0 := by
        by_contra hne
        apply hmem
        have hc : ev x ∈ ev '' tsupport g := by
          by_contra hc
          exact hne (hFzero _ hc)
        exact Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset hfin).2 ⟨ev x, hc, rfl⟩, hne⟩
      rw [hgx, h0]
      rfl
  have hmem : (∑ v ∈ Vs, Pm ev ι (φv v) (rep v) g) ∈
      Submodule.span ℂ {f | ∃ φ ∈ SB K, ∃ y, f = Pm ev ι φ y g} :=
    Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨φv v, hφv v hv, rep v, rfl⟩
  rwa [← hsum] at hmem

end PositivityTheory.ThKH.Locrep
