import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

namespace E4

section Gen

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem ev_shift {p : Deg k → Prop} (d : Deg k) (h : ∀ᶠ m in atTop, p m) :
    ∀ᶠ m in atTop, p (m - d) := by
  rw [eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  exact ⟨a + d, fun b hb => ha _ (le_sub_iff_add_le.mpr hb)⟩

theorem chi_ev_zero (ts : List (Deg k × R)) : ∀ (F : GMod B R k),
    (∀ᶠ m in atTop, F.gr m = ⊥) → ∀ᶠ m in atTop, chi ts F m = 0 := by
  induction ts with
  | nil =>
    intro F h
    filter_upwards [h] with m hm
    show ((Module.length B (F.gr m)).toNat : ℤ) = 0
    rw [hm]
    simp
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F h
    have h1 : ∀ᶠ m in atTop, (F.quot s).gr m = ⊥ := by
      filter_upwards [h] with m hm
      show (F.gr m).map _ = ⊥
      rw [hm, Submodule.map_bot]
    have h2 : ∀ᶠ m in atTop, (F.ann s d).gr m = ⊥ := by
      filter_upwards [ev_shift d h] with m hm
      show (F.gr (m - d)).comap _ = ⊥
      rw [hm]
      exact LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _)
    filter_upwards [ih _ h1, ih _ h2] with m a b
    simp [chi, a, b]

theorem ann_le_sub (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.sub N).Ann := by
  intro a ha
  refine Module.mem_annihilator.mpr fun x => ?_
  have hx : ∀ x : N, a • x = 0 := fun x => Subtype.ext (Module.mem_annihilator.mp ha x.1)
  exact hx x

theorem ann_le_quo (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.quo N).Ann := by
  intro a ha
  refine Module.mem_annihilator.mpr fun x => ?_
  have hx : ∀ x : F.M ⧸ N, a • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Module.mem_annihilator.mp ha y, Submodule.Quotient.mk_zero]
  exact hx x

theorem ann_sup_le_quot (F : GMod B R k) (σ : R) : F.Ann ⊔ Ideal.span {σ} ≤ (F.quot σ).Ann := by
  refine sup_le (ann_le_quo F _) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  refine Module.mem_annihilator.mpr fun x => ?_
  have hx : ∀ x : F.M ⧸ LinearMap.range (LinearMap.lsmul R F.M σ), σ • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  exact hx x

def isoTop (F : GMod B R k) (N : Submodule R F.M) (h : N = ⊤) : GIso (F.sub N) F where
  e := LinearEquiv.ofTop N h
  map_gr m := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h ▸ Submodule.mem_top⟩, hx, rfl⟩

def isoAnn (F : GMod B R k) (s : R) (d : Deg k) (h : ∀ x : F.M, s • x = 0) :
    GIso (F.ann s d) (F.shift d) where
  e := LinearEquiv.ofTop (LinearMap.ker (LinearMap.lsmul R F.M s))
    (by rw [eq_top_iff]; intro x _; exact h x)
  map_gr m := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h x⟩, hx, rfl⟩

def isoQuot (F : GMod B R k) (s : R) (h : ∀ x : F.M, s • x = 0) : GIso F (F.quot s) where
  e := (Submodule.quotEquivOfEqBot (LinearMap.range (LinearMap.lsmul R F.M s))
    (by rw [eq_bot_iff]; rintro _ ⟨x, rfl⟩; exact h x)).symm
  map_gr m := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩

theorem secs_cons_le (d : Deg k) (s : R) (ts : List (Deg k × R)) :
    secs ((d, s) :: ts) ≤ Ideal.span {s} ⊔ secs ts := by
  refine Ideal.span_le.mpr ?_
  rintro x ⟨d', hx⟩
  rcases List.mem_cons.mp hx with h | h
  · have : x = s := congrArg Prod.snd h
    subst this
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  · exact Ideal.mem_sup_right (Ideal.subset_span ⟨d', h⟩)

end Gen

section Graded

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (𝒜 : Deg k → Submodule B R)

theorem admissible_mono_ideal [IsLocalRing B] {ts : List (Deg k × R)} {J J' : Ideal R} (h : J ≤ J')
    (hA : admitted 𝒜 ts J) : admitted 𝒜 ts J' := by
  obtain ⟨N, hN⟩ := hA
  exact ⟨N, hN.trans (sup_le_sup_right h _)⟩

theorem admissible_tail_of_cons_mem [IsLocalRing B] {d : Deg k} {s : R} {ts : List (Deg k × R)} {J : Ideal R}
    (hA : admitted 𝒜 ((d, s) :: ts) J) : admitted 𝒜 ts (J ⊔ Ideal.span {s}) := by
  obtain ⟨N, hN⟩ := hA
  refine ⟨N, hN.trans ?_⟩
  rw [sup_assoc]
  exact sup_le_sup_left (secs_cons_le d s ts) _

variable [GradedAlgebra 𝒜]

theorem dimLT_mono {p : ℕ} {J J' : Ideal R} (h : J ≤ J') (hD : DimLT 𝒜 p J) : DimLT 𝒜 p J' := by
  cases p with
  | zero => exact fun 𝔮 hq hJ => hD 𝔮 hq (h.trans hJ)
  | succ p => exact fun 𝔮 hq hJ => hD 𝔮 hq (h.trans hJ)

theorem self_isGr : (GMod.self 𝒜).IsGr 𝒜 where
  smul_mem := fun ha hx => SetLike.mul_mem_graded (A := 𝒜) ha hx
  internal := DirectSum.Decomposition.isInternal 𝒜
  fin := Module.Finite.self R

theorem isHomSub_of_hom {𝔮 : Ideal R} (h : 𝔮.IsHomogeneous 𝒜) : (GMod.self 𝒜).IsHomSub 𝔮 := by
  classical
  have h2 : 𝔮 = Submodule.span R {x : R | x ∈ 𝔮 ∧ ∃ m, x ∈ 𝒜 m} := by
    apply le_antisymm
    · intro x hx
      rw [← DirectSum.sum_support_decompose 𝒜 x]
      exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨h i hx, i, SetLike.coe_mem _⟩
    · exact Submodule.span_le.mpr fun x hx => hx.1
  exact h2

theorem le_ann_quo (𝔮 : Ideal R) : 𝔮 ≤ ((GMod.self 𝒜).quo 𝔮).Ann := by
  intro a ha
  refine Module.mem_annihilator.mpr fun x => ?_
  have hx : ∀ x : R ⧸ (𝔮 : Submodule R R), a • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact 𝔮.mul_mem_right y ha
  exact hx x

theorem zero_on_quo {𝔮 : Ideal R} {s : R} (hs : s ∈ 𝔮) (x : ((GMod.self 𝒜).quo 𝔮).M) : s • x = 0 :=
  Module.mem_annihilator.mp (le_ann_quo 𝒜 𝔮 hs) x

theorem nzd_on_quo {𝔮 : Ideal R} (hp : 𝔮.IsPrime) {σ : R} (hn : σ ∉ 𝔮)
    (x : ((GMod.self 𝒜).quo 𝔮).M) (h : σ • x = 0) : x = 0 := by
  have hx : ∀ x : R ⧸ (𝔮 : Submodule R R), σ • x = 0 → x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    exact fun h => (hp.mem_or_mem h).resolve_left hn
  exact hx x h

theorem exists_sec {𝔮 : Ideal R} (h : IsRel 𝒜 𝔮) {d : Deg k} (hd : 0 ≤ d) : ∃ σ ∈ 𝒜 d, σ ∉ 𝔮 := by
  have h1 : ∀ i, ∃ τ ∈ 𝒜 (e i), τ ∉ 𝔮 := by
    intro i
    by_contra hc
    push Not at hc
    apply h.rel
    calc Irr 𝒜 ≤ Ideal.span (𝒜 (e i) : Set R) :=
          Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
      _ ≤ 𝔮 := Ideal.span_le.mpr hc
  choose τ hτ hτn using h1
  refine ⟨∏ i, τ i ^ (d i).toNat, ?_, ?_⟩
  · have h2 := SetLike.prod_mem_graded 𝒜 (fun i => (d i).toNat • e i) (fun i => τ i ^ (d i).toNat)
      (F := Finset.univ) (fun i _ => SetLike.pow_mem_graded _ (hτ i))
    have h3 : ∑ i, (d i).toNat • (e i : Deg k) = d := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      exact hd j
    rwa [h3] at h2
  · intro hc
    obtain ⟨i, _, hi⟩ := (h.prime.prod_mem_iff).mp hc
    exact hτn i (h.prime.mem_of_pow_mem _ hi)

theorem comp_of_mul {𝔮 : Ideal R} (hp : 𝔮.IsPrime) (hh : 𝔮.IsHomogeneous 𝒜) {d : Deg k} {σ : R}
    (hσ : σ ∈ 𝒜 d) (hn : σ ∉ 𝔮) (m : Deg k) (r a : R) (ha : a ∈ 𝒜 m) (h : σ * r - a ∈ 𝔮) :
    r - (DirectSum.decompose 𝒜 r (m - d) : R) ∈ 𝔮 := by
  classical
  have key : ∀ j, j ≠ m - d → (DirectSum.decompose 𝒜 r j : R) ∈ 𝔮 := by
    intro j hj
    have h1 := hh (d + j) h
    have hne : m ≠ d + j := by
      intro hc
      apply hj
      rw [hc]
      abel
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hσ, DirectSum.decompose_of_mem_ne 𝒜 ha hne,
      sub_zero] at h1
    exact (hp.mem_or_mem h1).resolve_left hn
  rw [← DirectSum.sum_support_decompose 𝒜 (r - (DirectSum.decompose 𝒜 r (m - d) : R))]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, DirectSum.decompose_coe]
  by_cases hj : j = m - d
  · subst hj
    rw [DirectSum.of_eq_same, sub_self]
    exact 𝔮.zero_mem
  · rw [DirectSum.of_eq_of_ne _ _ _ hj, Submodule.coe_zero, sub_zero]
    exact key j hj

def sesMul {𝔮 : Ideal R} (hp : 𝔮.IsPrime) (hh : 𝔮.IsHomogeneous 𝒜) {d : Deg k} {σ : R}
    (hσ : σ ∈ 𝒜 d) (hn : σ ∉ 𝔮) :
    SES (((GMod.self 𝒜).quo 𝔮).shift d) ((GMod.self 𝒜).quo 𝔮) (((GMod.self 𝒜).quo 𝔮).quot σ) where
  f := LinearMap.lsmul R ((GMod.self 𝒜).quo 𝔮).M σ
  g := (LinearMap.range (LinearMap.lsmul R ((GMod.self 𝒜).quo 𝔮).M σ)).mkQ
  inj := (injective_iff_map_eq_zero _).mpr fun x hx => nzd_on_quo 𝒜 hp hn x hx
  surj := Submodule.mkQ_surjective _
  exact := LinearMap.exact_map_mkQ_range _
  f_gr m := by
    ext x
    constructor
    · rintro ⟨r', hr, rfl⟩
      obtain ⟨r, rfl⟩ : ∃ r : R, r = r' := ⟨r', rfl⟩
      have hr' : r ∈ 𝒜 (m - d) := hr
      refine ⟨(σ * r : R), ?_, rfl⟩
      have := SetLike.mul_mem_graded (A := 𝒜) hσ hr'
      rwa [add_sub_cancel] at this
    · rintro ⟨a', ha', hax⟩
      obtain ⟨r', rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨a, rfl⟩ : ∃ a : R, a = a' := ⟨a', rfl⟩
      obtain ⟨r, rfl⟩ : ∃ r : R, r = r' := ⟨r', rfl⟩
      have ha : a ∈ 𝒜 m := ha'
      refine ⟨(DirectSum.decompose 𝒜 r (m - d) : R), SetLike.coe_mem _, ?_⟩
      have h1 : σ * r - a ∈ 𝔮 := by
        have h2 : Submodule.Quotient.mk (p := (𝔮 : Submodule R R)) a
            = Submodule.Quotient.mk (p := (𝔮 : Submodule R R)) (σ * r) := hax
        exact (Submodule.Quotient.eq _).mp h2.symm
      exact ((Submodule.Quotient.eq (𝔮 : Submodule R R)).mpr
        (comp_of_mul 𝒜 hp hh hσ hn m r a ha h1)).symm
  g_gr m := rfl

end Graded

section Main

theorem dev_reduce (hGr : RuleGr) (hIrr : RuleIrr) (hIso : RuleIso) (hShift : RuleShift)
    (hE1 : EulerAdditivityExactSequence) (hDev : RuleDev) {P : ℤ → Prop} (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R))
    (F : X.Mod) (hv : Valid X.𝒜 ts) (hF : F.IsGr X.𝒜) (hA : admitted X.𝒜 ts F.Ann)
    (H : ∀ 𝔮 : Ideal X.R, IsRel X.𝒜 𝔮 → F.Ann ≤ 𝔮 →
      ∀ᶠ m in atTop, P (chi ts ((GMod.self X.𝒜).quo 𝔮) m)) :
    ∀ᶠ m in atTop, P (chi ts F m) := by
  obtain ⟨t, N, 𝔮, d, hN0, hNt, hhom, -, hstep⟩ := hDev k X F hF
  have key : ∀ i, i ≤ t → ∀ᶠ m in atTop, P (chi ts (F.sub (N i)) m) := by
    intro i
    induction i with
    | zero =>
      intro _
      have h1 : ∀ᶠ m in atTop, chi ts (F.sub (N 0)) m = 0 := by
        apply chi_ev_zero
        refine Eventually.of_forall fun m => ?_
        rw [hN0, Submodule.eq_bot_iff]
        intro x _
        have hx : ∀ x : (⊥ : Submodule X.R F.M), x = 0 :=
          fun x => Subtype.ext ((Submodule.mem_bot _).mp x.2)
        exact hx x
      filter_upwards [h1] with m hm
      rw [hm]
      exact h0
    | succ i ih =>
      intro hi
      obtain ⟨hp, hh, hle, ⟨ses⟩⟩ := hstep i hi
      have g1 := ((hGr k X F hF).1 (N i) (hhom i)).1
      have g2 := ((hGr k X F hF).1 (N (i + 1)) (hhom (i + 1))).1
      have g0 : ((GMod.self X.𝒜).quo (𝔮 i)).IsGr X.𝒜 :=
        ((hGr k X _ (self_isGr X.𝒜)).1 (𝔮 i) (isHomSub_of_hom X.𝒜 hh)).2
      have g3 : (((GMod.self X.𝒜).quo (𝔮 i)).shift (d i)).IsGr X.𝒜 := (hGr k X _ g0).2.1 (d i)
      have hs := hE1 k X ts _ _ _ hv g1 g2 g3 ses (admissible_mono_ideal X.𝒜 (ann_le_sub F _) hA)
      have hq : ∀ᶠ m in atTop, P (chi ts ((GMod.self X.𝒜).quo (𝔮 i)) m) := by
        by_cases hrel : Irr X.𝒜 ≤ 𝔮 i
        · have hz := chi_ev_zero ts _ (hIrr k X _ g0
            ⟨1, by rw [pow_one]; exact hrel.trans (le_ann_quo X.𝒜 (𝔮 i))⟩)
          filter_upwards [hz] with m hm
          rw [hm]
          exact h0
        · exact H (𝔮 i) ⟨hp, hh, hrel⟩ hle
      filter_upwards [hs, ih (Nat.le_of_succ_le hi), ev_shift (d i) hq] with m a b c
      rw [a]
      refine hadd _ _ b ?_
      rw [hShift]
      exact c
  filter_upwards [key t le_rfl] with m hm
  rwa [hIso k X ts _ _ (isoTop F (N t) hNt) m] at hm

theorem prime_step (hGr : RuleGr) (hIso : RuleIso) (hNzd : RuleNzd) (hE1 : EulerAdditivityExactSequence) {k : ℕ}
    (X : HidaSetting k) (𝔮 : Ideal X.R) (hq : IsRel X.𝒜 𝔮) (d : Deg k) (s : X.R)
    (ts : List (Deg k × X.R)) (hv : Valid X.𝒜 ((d, s) :: ts)) (hA : admitted X.𝒜 ((d, s) :: ts) 𝔮) :
    ∃ σ ∈ X.𝒜 d, σ ∉ 𝔮 ∧ admitted X.𝒜 ts (𝔮 ⊔ Ideal.span {σ}) ∧
      ∀ᶠ m in atTop, chi ((d, s) :: ts) ((GMod.self X.𝒜).quo 𝔮) m
        = chi ts (((GMod.self X.𝒜).quo 𝔮).quot σ) m := by
  obtain ⟨hd, hs⟩ := hv (d, s) List.mem_cons_self
  have hv' : Valid X.𝒜 ts := fun p hp => hv p (List.mem_cons_of_mem _ hp)
  by_cases hsq : s ∈ 𝔮
  · obtain ⟨σ, hσ, hn⟩ := exists_sec X.𝒜 hq hd
    have hA' : admitted X.𝒜 ts 𝔮 := by
      refine admissible_mono_ideal X.𝒜 ?_ (admissible_tail_of_cons_mem X.𝒜 hA)
      exact sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).mpr hsq)
    refine ⟨σ, hσ, hn, admissible_mono_ideal X.𝒜 le_sup_left hA', ?_⟩
    have g0 : ((GMod.self X.𝒜).quo 𝔮).IsGr X.𝒜 :=
      ((hGr k X _ (self_isGr X.𝒜)).1 𝔮 (isHomSub_of_hom X.𝒜 hq.hom)).2
    have g1 := (hGr k X _ g0).2.1 d
    have g2 := ((hGr k X _ g0).2.2 d σ hσ).1
    have hs := hE1 k X ts _ _ _ hv' g1 g0 g2 (sesMul X.𝒜 hq.prime hq.hom hσ hn)
      (admissible_mono_ideal X.𝒜 (le_ann_quo X.𝒜 𝔮) hA')
    filter_upwards [hs] with m hm
    have e1 := hIso k X ts _ _ (isoQuot ((GMod.self X.𝒜).quo 𝔮) s (zero_on_quo X.𝒜 hsq)) m
    have e2 := hIso k X ts _ _ (isoAnn ((GMod.self X.𝒜).quo 𝔮) s d (zero_on_quo X.𝒜 hsq)) m
    show chi ts (((GMod.self X.𝒜).quo 𝔮).quot s) m - chi ts (((GMod.self X.𝒜).quo 𝔮).ann s d) m = _
    rw [← e1, e2, hm]
    ring
  · refine ⟨s, hs, hsq, admissible_tail_of_cons_mem X.𝒜 hA, Eventually.of_forall fun m => ?_⟩
    exact hNzd k X ts _ d s (nzd_on_quo X.𝒜 hq.prime hsq) m

theorem core (hGr : RuleGr) (hIrr : RuleIrr) (hIso : RuleIso) (hShift : RuleShift)
    (hNzd : RuleNzd) (hE1 : EulerAdditivityExactSequence) (hDev : RuleDev) {P : ℤ → Prop} (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (c : ℕ)
    (hbase : ∀ (k : ℕ) (X : HidaSetting k) (𝔮 : Ideal X.R), IsRel X.𝒜 𝔮 → DimLT X.𝒜 c 𝔮 →
      ∀ m, P (chi [] ((GMod.self X.𝒜).quo 𝔮) m))
    (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) : ∀ (F : X.Mod), Valid X.𝒜 ts →
    F.IsGr X.𝒜 → admitted X.𝒜 ts F.Ann → DimLT X.𝒜 (ts.length + c) F.Ann →
    ∀ᶠ m in atTop, P (chi ts F m) := by
  induction ts with
  | nil =>
    intro F hv hF hA hD
    refine dev_reduce hGr hIrr hIso hShift hE1 hDev h0 hadd X [] F hv hF hA fun 𝔮 hq hle => ?_
    have hD' : DimLT X.𝒜 c F.Ann := by simpa using hD
    exact Eventually.of_forall (hbase k X 𝔮 hq (dimLT_mono X.𝒜 hle hD'))
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hv hF hA hD
    refine dev_reduce hGr hIrr hIso hShift hE1 hDev h0 hadd X _ F hv hF hA fun 𝔮 hq hle => ?_
    obtain ⟨σ, hσ, hn, hAσ, hev⟩ :=
      prime_step hGr hIso hNzd hE1 X 𝔮 hq d s ts hv (admissible_mono_ideal X.𝒜 hle hA)
    have hD' : DimLT X.𝒜 (ts.length + c + 1) F.Ann := by
      have : ((d, s) :: ts).length + c = ts.length + c + 1 := by
        rw [List.length_cons]; omega
      rwa [this] at hD
    have hDσ : DimLT X.𝒜 (ts.length + c) (𝔮 ⊔ Ideal.span {σ}) := hD' 𝔮 hq hle d σ hσ hn
    have g0 : ((GMod.self X.𝒜).quo 𝔮).IsGr X.𝒜 :=
      ((hGr k X _ (self_isGr X.𝒜)).1 𝔮 (isHomSub_of_hom X.𝒜 hq.hom)).2
    have hle' : 𝔮 ⊔ Ideal.span {σ} ≤ (((GMod.self X.𝒜).quo 𝔮).quot σ).Ann :=
      (sup_le_sup_right (le_ann_quo X.𝒜 𝔮) _).trans (ann_sup_le_quot _ σ)
    have := ih (((GMod.self X.𝒜).quo 𝔮).quot σ) (fun p hp => hv p (List.mem_cons_of_mem _ hp))
      ((hGr k X _ g0).2.2 d σ hσ).1 (admissible_mono_ideal X.𝒜 hle' hAσ) (dimLT_mono X.𝒜 hle' hDσ)
    filter_upwards [hev, this] with m a b
    rw [a]
    exact b

end Main

end E4

end Formalism.MainNotions.V.Pf.V2.Calc
