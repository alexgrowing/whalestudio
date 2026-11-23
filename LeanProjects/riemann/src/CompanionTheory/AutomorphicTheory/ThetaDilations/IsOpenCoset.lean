import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)

def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)

omit [TopologicalSpace V] in
theorem ind_of_mem {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 :=
  Set.indicator_of_mem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
theorem ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 :=
  Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
theorem ind_congr {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (h.1 hx)]
  · rw [ind_of_not hx, ind_of_not (mt h.2 hx)]

omit [TopologicalSpace V] in
theorem ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x :=
  ind_congr (by rw [add_sub_right_comm, L.add_mem_cancel_right hl])

section top

variable [IsTopologicalAddGroup V]

theorem CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') :=
  ⟨by rw [AddSubgroup.add_normal]; exact h.1.add h'.1, AddSubgroup.isOpen_mono le_sup_left h.2⟩

theorem CO.inf {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') :=
  ⟨h.1.inter_right (L'.isClosed_of_isOpen h'), h.2.inter h'⟩

theorem isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} :=
  h.preimage (continuous_id.sub continuous_const)

theorem lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f :=
  (IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by
    have := hf x _ hy
    rwa [add_sub_cancel] at this⟩

theorem sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  refine ⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L)
    (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]
  · rw [ind_of_not hx, ind_of_not fun h' => hx (by
      rw [add_sub_right_comm] at h'; exact (L.add_mem_cancel_right hl).1 h')]

end top

omit [AddCommGroup V] in
theorem sb_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : SB (f + g) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

omit [AddCommGroup V] in
theorem sb_mul {f g : V → ℂ} (hf : IsLocallyConstant f) (hg : SB g) : SB fun x => f x * g x :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

omit [AddCommGroup V] in
theorem sb_smul (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := sb_mul (IsLocallyConstant.const c) hg

omit [AddCommGroup V] in
theorem sb_zero : SB (0 : V → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

omit [AddCommGroup V] in
theorem sb_sum {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) :=
  Finset.sum_induction _ SB (fun _ _ => sb_add) sb_zero h

omit [AddCommGroup V] in
theorem sb_homeo {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem sb_span [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L := by
  classical
  have := QuotientAddGroup.discreteTopology hL
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ L) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine ⟨hfin.toFinset.image Quotient.out, funext fun x => ?_⟩
  have hq : ∀ c : V ⧸ L, x - c.out ∈ L ↔ c = QuotientAddGroup.mk x := fun c => by
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', eq_comm]
  rw [Finset.sum_apply, Finset.sum_image fun a _ b _ h => Quotient.out_injective h]
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ (Finset.sum_eq_single (QuotientAddGroup.mk x : V ⧸ L) (fun c _ hc => ?_) fun hx => ?_).symm
  · have := hinv (QuotientAddGroup.mk x : V ⧸ L).out _ ((hq _).2 rfl)
    rw [add_sub_cancel] at this
    rw [ind_of_mem ((hq _).2 rfl), mul_one, this]
  · rw [ind_of_not (mt (hq c).1 hc), mul_zero]
  · have h0 : φ (QuotientAddGroup.mk x : V ⧸ L).out = 0 := by
      by_contra hne
      exact hx (hfin.mem_toFinset.2 ⟨_, subset_tsupport _ hne, QuotientAddGroup.out_eq' _⟩)
    rw [h0, zero_mul]

variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}

theorem co_cpt (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by
  obtain ⟨_, -, -, -, -, -, -, hbig, -⟩ := h
  refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, CO L ∧ s ⊆ L) ?_ ?_ ?_ ?_
  · obtain ⟨L, h1, h2, -⟩ := hbig 0
    exact ⟨L, ⟨h1, h2⟩, empty_subset _⟩
  · rintro s t hst ⟨L, h1, h2⟩
    exact ⟨L, h1, hst.trans h2⟩
  · rintro s t ⟨L, h1, h2⟩ ⟨L', h1', h2'⟩
    exact ⟨L ⊔ L', h1.sup h1', union_subset (h2.trans (SetLike.coe_subset_coe.2 le_sup_left))
      (h2'.trans (SetLike.coe_subset_coe.2 le_sup_right))⟩
  · intro x _
    obtain ⟨L, h1, h2, h3⟩ := hbig x
    exact ⟨L, mem_nhdsWithin_of_mem_nhds (h2.mem_nhds h3), L, ⟨h1, h2⟩, le_rfl⟩

theorem sb_level (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  obtain ⟨L, hL, hKL⟩ := co_cpt h hφ.2.isCompact
  obtain ⟨_, -, -, -, -, -, hsmall, -⟩ := h
  have h0 : ∀ x, x ∉ L → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h' => hx (hKL h')
  have key : ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ (L : Set V), ∀ l ∈ L', φ (x + l) = φ x := by
    refine hL.1.induction_on
      (p := fun s => ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ s, ∀ l ∈ L', φ (x + l) = φ x) ?_ ?_ ?_ ?_
    · exact ⟨⊤, isOpen_univ, fun _ h => absurd h (notMem_empty _)⟩
    · rintro s t hst ⟨L', h1, h2⟩
      exact ⟨L', h1, fun x hx => h2 x (hst hx)⟩
    · rintro s t ⟨L₁, h1, h2⟩ ⟨L₂, h1', h2'⟩
      exact ⟨L₁ ⊓ L₂, h1.inter h1', fun x hx l hl => hx.elim (fun h => h2 x h l hl.1) fun h => h2' x h l hl.2⟩
    · intro x _
      have hU : {y | φ (x + y) = φ x} ∈ 𝓝 (0 : V) := by
        have h1 : ContinuousAt (fun y => x + y) 0 := (continuous_const.add continuous_id).continuousAt
        exact h1.preimage_mem_nhds (by rw [add_zero]; exact hφ.1.eventually_eq x)
      obtain ⟨L₀, -, h2, h3⟩ := hsmall _ hU
      refine ⟨{y | y - x ∈ L₀}, mem_nhdsWithin_of_mem_nhds ((isOpen_coset x h2).mem_nhds (by simp)), L₀, h2,
        fun y hy l hl => ?_⟩
      have e1 : φ (x + (y - x + l)) = φ x := h3 (L₀.add_mem hy hl)
      have e2 : φ (x + (y - x)) = φ x := h3 hy
      rw [add_sub_cancel] at e2
      rw [← add_assoc, add_sub_cancel] at e1
      rw [e1, e2]
  obtain ⟨L', h1, h2⟩ := key
  refine ⟨L, L ⊓ L', hL, hL.inf h1, inf_le_left, h0, fun x l hl => ?_⟩
  by_cases hx : x ∈ L
  · exact h2 x hx l hl.2
  · rw [h0 x hx, h0 _ fun h' => hx ((L.add_mem_cancel_right hl.1).1 h')]

section chi

variable (h : NADual V χ μ)
include h

theorem chi_sym (x y : V) : χ x y = χ y x := h.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_norm (x y : V) : ‖χ x y‖ = 1 := h.2.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_add (x x' y : V) : χ (x + x') y = χ x y * χ x' y := h.2.2.2.2.2.2.2.2.2.2.2.1 x x' y
theorem chi_cont : Continuous fun p : V × V => χ p.1 p.2 := h.2.2.2.2.2.2.2.2.1
theorem chi_ne (x y : V) : χ x y ≠ 0 := norm_ne_zero_iff.1 (by rw [chi_norm h]; exact one_ne_zero)
theorem chi_add' (x y y' : V) : χ x (y + y') = χ x y * χ x y' := by
  rw [chi_sym h, chi_add h, chi_sym h y, chi_sym h y']
theorem chi_zero (y : V) : χ 0 y = 1 :=
  mul_left_cancel₀ (chi_ne h 0 y) (by rw [← chi_add h, add_zero, mul_one])
theorem chi_neg (x y : V) : χ (-x) y = conj (χ x y) := by
  refine mul_left_cancel₀ (chi_ne h x y) ?_
  rw [← chi_add h, add_neg_cancel, chi_zero h, Complex.mul_conj', chi_norm h]; simp

def perpG (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  zero_mem' := fun x _ => by rw [chi_sym h, chi_zero h]
  add_mem' := fun ha hb x hx => by rw [chi_add' h, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {y} hy x hx => by rw [chi_sym h, chi_neg h, chi_sym h, hy x hx, map_one]

theorem co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) :=
  ⟨(h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).1, (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.1⟩

theorem perp_perp {L : AddSubgroup V} (hL : CO L) (x : V) : x ∈ perpG h (perpG h L) ↔ x ∈ L :=
  ⟨fun hx => (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.1 hx, fun hx y hy => by rw [chi_sym h]; exact hy x hx⟩

theorem meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by
  rw [← ENNReal.toReal_mul]
  exact (congrArg ENNReal.toReal (h.2.2.2.2.2.2.2.2.2.2.2.2 L hL.1 hL.2).2.2.2).trans ENNReal.toReal_one

theorem chi_lc (a : V) : IsLocallyConstant fun y => χ a y := by
  have := h.1
  obtain ⟨L, hL, ha⟩ := co_cpt h (isCompact_singleton (x := a))
  exact lc_of_inv (co_perp h hL).2 fun x l hl => by rw [chi_add' h, hl a (ha rfl), mul_one]

theorem sb_int {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  obtain ⟨_, _, _, _, _, _, -⟩ := h
  exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2

theorem sb_chi {φ : V → ℂ} (hφ : SB φ) (y : V) : SB fun x => φ x * χ x y := by
  simpa only [mul_comm, chi_sym h y] using sb_mul (chi_lc h y) hφ

theorem fou_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : fou χ μ (f + g) = fou χ μ f + fou χ μ g := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_int h (sb_chi h hf y)) (sb_int h (sb_chi h hg y))

omit h in
theorem fou_smul (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

omit h [AddCommGroup V] [MeasurableSpace V] in
theorem map_sum_sb {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsm 0 0 sb_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (sb_smul _ (hf a)) (sb_sum _ fun b _ => sb_smul _ (hf b)),
      hsm _ _ (hf a), ih]

theorem fou_ind {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  have e1 : fou χ μ (ind a L) y = χ a y * ∫ x, ind 0 L x * χ x y ∂μ := by
    rw [fou, ← integral_add_right_eq_self _ a, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [chi_add h]
    rw [ind_congr (b := 0) (y := x) (L' := L) (by rw [add_sub_cancel_right, sub_zero])]
    ring
  rw [e1]
  by_cases hy : y ∈ perpG h L
  · rw [ind_of_mem (by simpa using hy)]
    have e2 : (fun x => ind 0 L x * χ x y) = Set.indicator (L : Set V) fun _ => (1 : ℂ) := by
      funext x
      by_cases hx : x ∈ L
      · rw [ind_of_mem (by simpa using hx), hy x hx, Set.indicator_of_mem (s := (L : Set V)) hx, one_mul]
      · rw [ind_of_not (by simpa using hx), Set.indicator_of_notMem (s := (L : Set V)) hx, zero_mul]
    rw [e2, integral_indicator_const _ hL.2.measurableSet]
    simp [Measure.real, mul_comm]
  · rw [ind_of_not (by simpa using hy), mul_zero]
    obtain ⟨l, hl, hne⟩ : ∃ l ∈ L, χ l y ≠ 1 := by
      by_contra h'
      push Not at h'
      exact hy h'
    have e2 : ∫ x, ind 0 L x * χ x y ∂μ = χ l y * ∫ x, ind 0 L x * χ x y ∂μ := by
      conv_lhs => rw [← integral_add_right_eq_self _ l]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [chi_add h, ind_add x hl]
      ring
    have e3 : (1 - χ l y) * ∫ x, ind 0 L x * χ x y ∂μ = 0 := by rw [sub_mul, one_mul, ← e2, sub_self]
    rw [(mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 hne.symm), mul_zero]

theorem fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
  have hP := co_perp h hL
  have e1 : ∀ a, fou χ μ (ind a L) = ((μ L).toReal : ℂ) • fun y => ind 0 (perpG h L) y * χ y a := fun a => by
    funext y
    rw [fou_ind h hL, Pi.smul_apply, smul_eq_mul, chi_sym h y]; ring
  have e2 : ∀ a, SB (fou χ μ (ind a L)) := fun a => e1 a ▸ sb_smul _ (sb_chi h (sb_ind 0 hP) a)
  have e3 : fou χ μ φ = ∑ a ∈ s, φ a • fou χ μ (ind a L) := by
    conv_lhs => rw [hs]
    exact map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ fun a => sb_ind a hL
  refine ⟨e3 ▸ sb_sum _ fun a _ => sb_smul _ (e2 a), fun x => ?_⟩
  rw [e3, map_sum_sb (fun _ _ => fou_add h) (fun c f _ => fou_smul c f) s φ e2]
  conv_rhs => rw [hs]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ?_
  have e4 : fou χ μ (fun y => ind 0 (perpG h L) y * χ y a) x = fou χ μ (ind 0 (perpG h L)) (a + x) := by
    simp only [fou, chi_add' h, mul_assoc]
  rw [e1, fou_smul, Pi.smul_apply, e4, fou_ind h hP, chi_zero h, mul_one, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    meas_perp h hL, Complex.ofReal_one, one_mul]
  have e5 : a + x - 0 ∈ perpG h (perpG h L) ↔ -x - a ∈ L := by
    rw [perp_perp h hL, ← L.neg_mem_iff, sub_zero, neg_add_rev, sub_eq_add_neg]
  by_cases hx : -x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (e5.2 hx)]
  · rw [ind_of_not hx, ind_of_not (mt e5.1 hx)]

theorem planch {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  obtain ⟨hF, hinv⟩ := fou_sb h hφ
  have hc : Integrable (fun x => conj (φ x)) μ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sb_int h hφ)
  have hint : Integrable (Function.uncurry fun y x => fou χ μ φ y * conj (φ x) * χ y (-x)) (μ.prod μ) :=
    ((sb_int h hF).mul_prod hc).mul_bdd (c := 1)
      ((chi_cont h).comp (continuous_fst.prodMk continuous_snd.neg)).aestronglyMeasurable
      (ae_of_all _ fun p => (chi_norm h _ _).le)
  have e := integral_integral_swap hint
  have e1 : ∀ y, ∫ x, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖fou χ μ φ y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    simp only [mul_assoc, integral_const_mul]
    rw [Complex.ofReal_pow, ← Complex.mul_conj', fou, ← integral_conj]
    congr 2
    funext x
    rw [map_mul, chi_sym h y, chi_neg h]
  have e2 : ∀ x, ∫ y, fou χ μ φ y * conj (φ x) * χ y (-x) ∂μ = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    have := hinv (-x)
    rw [neg_neg, fou] at this
    simp only [mul_right_comm _ (conj (φ x)), integral_mul_const]
    rw [this, Complex.ofReal_pow, Complex.mul_conj']
  simp only [e1, e2, integral_ofReal] at e
  exact_mod_cast e

theorem schur {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hch : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) : ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  have hh := h
  obtain ⟨_, _, -⟩ := hh
  have h1 : ∀ L : AddSubgroup V, CO L → ∀ a, T (ind a L) = T (ind 0 L) 0 • ind a L := by
    intro L hL a
    have e : ind a L = fun u => ind 0 L (u + -a) := funext fun u => ind_congr (by rw [sub_zero, sub_eq_add_neg])
    rw [e, htr _ _ (sb_ind 0 hL)]
    funext u
    generalize_proofs
    simp only [Pi.smul_apply, smul_eq_mul]
    generalize u + -a = v
    by_cases hv : v ∈ L
    · have e2 : (fun u => ind 0 L (u + v)) = ind 0 L := funext fun u => ind_add u hv
      have := congrFun (htr v _ (sb_ind 0 hL)) 0
      rw [e2, zero_add] at this
      rw [ind_of_mem (by simpa using hv), mul_one, this]
    · rw [ind_of_not (by simpa using hv), mul_zero]
      by_contra hne
      refine hv ((perp_perp h hL v).1 fun y hy => ?_)
      have e2 : (fun u => χ u y * ind 0 L u) = ind 0 L := by
        funext u
        by_cases hu : u ∈ L
        · rw [hy u hu, one_mul]
        · rw [ind_of_not (by simpa using hu), mul_zero]
      have := congrFun (hch y _ (sb_ind 0 hL)) v
      rw [e2] at this
      rw [chi_sym h]
      exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  have h2 : ∀ L : AddSubgroup V, CO L → ∀ φ, SB φ → (∀ x, ∀ l ∈ L, φ (x + l) = φ x) → T φ = T (ind 0 L) 0 • φ := by
    intro L hL φ hφ hinv
    obtain ⟨s, hs⟩ := sb_span hφ hL.2 hinv
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [map_sum_sb hadd hsm s φ fun a => sb_ind a hL, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [h1 L hL a, smul_comm]
  obtain ⟨L₀, hL₀, -⟩ := co_cpt h isCompact_empty
  refine ⟨T (ind 0 L₀) 0, fun φ hφ => ?_⟩
  obtain ⟨-, L, -, hL, -, -, hinv⟩ := sb_level h hφ
  have h3 := congrFun (h2 _ (hL₀.inf hL.2) (ind 0 L₀) (sb_ind 0 hL₀) fun x l hl => ind_add x hl.1) 0
  rw [Pi.smul_apply, ind_of_mem (by simp), smul_eq_mul, mul_one] at h3
  rw [h3]
  exact h2 _ (hL₀.inf hL.2) φ hφ fun x l hl => hinv x l hl.2

end chi

end CompanionTheory.PlacePermOperatorBicommutantSpan
