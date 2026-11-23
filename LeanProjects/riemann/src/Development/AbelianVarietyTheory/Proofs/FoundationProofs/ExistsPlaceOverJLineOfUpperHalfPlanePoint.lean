import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.ValAt

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_germ_eq {τ : ℂ} (hτ : τ ∈ Hs) {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  rw [Filter.Germ.coe_eq] at h
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz hz'
  rcases hz with hz | hz
  · exact hz
  · exact absurd hz' hz

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.exists_rep (g : _root_.GlobalTheory.KZ.Mero) :
    ∃ φ : ℂ → ℂ, g = (φ : _root_.GlobalTheory.KZ.Mero) := by
  obtain ⟨φ, hφ⟩ := Quot.exists_rep g
  exact ⟨φ, hφ.symm⟩

def rep (X : Tower Ω ε) (x : X.K) : ℂ → ℂ := (exists_rep (X.an x)).choose

theorem rep_spec (X : Tower Ω ε) (x : X.K) : X.an x = (rep X x : Mero) := (exists_rep (X.an x)).choose_spec

def ord (X : Tower Ω ε) (τ : ℂ) (x : X.K) : WithTop ℤ := meromorphicOrderAt (rep X x) τ

theorem ord_eq (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) {x : X.K} {φ : ℂ → ℂ} (h : X.an x = (φ : Mero)) :
    ord X τ x = meromorphicOrderAt φ τ :=
  meromorphicOrderAt_congr (nhdsNE_of_germ_eq hτ ((rep_spec X x).symm.trans h))

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem an_eq_germ_rep (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) :
    X.an x = (_root_.GlobalTheory.KZ.ValAt.rep X x : _root_.GlobalTheory.KZ.Mero) :=
  (_root_.GlobalTheory.KZ.ValAt.exists_rep (X.an x)).choose_spec

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem isOpen_upperHalfPlaneSet' : IsOpen _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact isOpen_lt continuous_const Complex.continuous_im

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem eventuallyEq_nhdsNE_of_mero_coe_eq {φ ψ : ℂ → ℂ}
    (h : (φ : _root_.GlobalTheory.KZ.Mero) = ψ) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  have h' := (Filter.Germ.coe_eq.1 h : φ =ᶠ[codiscreteWithin _root_.GlobalTheory.KZ.Hs] ψ)
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at h'
  have hd := h' τ hτ
  rw [Filter.disjoint_principal_right] at hd
  filter_upwards [hd, nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet'.mem_nhds hτ)] with z h1 h2
  by_contra hne
  exact h1 ⟨h2, hne⟩

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem ord_eq_meromorphicOrderAt_of_an_eq_coe {φ : ℂ → ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) (h : X.an x = (φ : _root_.GlobalTheory.KZ.Mero)) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x = meromorphicOrderAt φ τ := by
  unfold _root_.GlobalTheory.KZ.ValAt.ord
  rw [an_eq_germ_rep] at h
  exact meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_mero_coe_eq h hτ)

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem isPreconnected_upperHalfPlaneSet : IsPreconnected _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact (convex_halfSpace_im_gt 0).isPreconnected

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero {b : ℂ → ℂ}
    (hb : DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs)
    (hb0 : (b : _root_.GlobalTheory.KZ.Mero) ≠ 0) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
  have ha := hb.analyticOnNhd isOpen_upperHalfPlaneSet'
  rcases (ha τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    apply hb0
    have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_upperHalfPlaneSet hτ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    exact Filter.eventually_of_mem (self_mem_codiscreteWithin _) hz
  · exact h

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem exists_differentiableOn_rep_eventuallyEq_div (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a _root_.GlobalTheory.KZ.Hs ∧
      DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs ∧
      _root_.GlobalTheory.KZ.ValAt.rep X x =ᶠ[𝓝[≠] τ] a / b := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  refine ⟨a, b, ha, hb, ?_⟩
  rw [an_eq_germ_rep, ← Filter.Germ.coe_mul] at hab
  filter_upwards [eventuallyEq_nhdsNE_of_mero_coe_eq hab hτ, eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero hb hb0 hτ]
    with z h1 h2
  rw [Pi.div_apply, eq_div_iff h2]
  exact h1

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem meromorphicAt_rep_of_mem_upperHalfPlaneSet (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    MeromorphicAt (_root_.GlobalTheory.KZ.ValAt.rep X x) τ := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_differentiableOn_rep_eventuallyEq_div X x hτ
  have ha' := (ha.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  have hb' := (hb.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  exact (ha'.div hb').congr h.symm

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_mul (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ (x * y) =
      _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ y := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x * y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x * _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_mul (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_mul, Filter.Germ.coe_mul, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_add (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    min (_root_.GlobalTheory.KZ.ValAt.ord X τ x) (_root_.GlobalTheory.KZ.ValAt.ord X τ y) ≤
      _root_.GlobalTheory.KZ.ValAt.ord X τ (x + y) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x + y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x + _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_add (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_add, Filter.Germ.coe_add, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_const (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (c : Ω) :
    0 ≤ _root_.GlobalTheory.KZ.ValAt.ord X τ (algebraMap Ω X.K c) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X _ (X.an_c c) hτ]
  exact analyticAt_const.meromorphicOrderAt_nonneg

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_one (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : _root_.GlobalTheory.KZ.ValAt.ord X τ 1 = 0 := by
  classical
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X 1 (φ := fun _ => 1) (by rw [map_one]; rfl) hτ,
    meromorphicOrderAt_const]
  simp

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_add_ord_inv (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) {x : X.K} (hx : x ≠ 0) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ x⁻¹ = 0 := by
  rw [← _root_.GlobalTheory.KZ.ValAt.ord_mul X hτ, mul_inv_cancel₀ hx,
    _root_.GlobalTheory.KZ.ValAt.ord_one X hτ]

def place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) : ValuationSubring X.K where
  carrier := {x | 0 ≤ ord X τ x}
  mul_mem' {x y} hx hy := by
    show 0 ≤ ord X τ (x * y)
    rw [ord_mul X hτ]
    exact add_nonneg hx hy
  one_mem' := (ord_one X hτ).ge
  add_mem' {x y} hx hy := (le_min hx hy).trans (ord_add X hτ x y)
  zero_mem' := by simpa using ord_const X hτ 0
  neg_mem' {x} hx := by
    show 0 ≤ ord X τ (-x)
    have h := ord_const X hτ (-1)
    rw [map_neg, map_one] at h
    rw [← neg_one_mul, ord_mul X hτ]
    exact add_nonneg h hx
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left
      subst hx
      show 0 ≤ ord X τ 0
      simpa using ord_const X hτ 0
    · by_contra hc
      rw [not_or] at hc
      have h1 : ord X τ x < 0 := not_le.1 hc.1
      have h2 : ord X τ x⁻¹ < 0 := not_le.1 hc.2
      have h3 := ord_add_ord_inv X hτ hx
      have h4 : ord X τ x + ord X τ x⁻¹ ≤ ord X τ x + 0 := by gcongr
      rw [h3, add_zero] at h4
      exact absurd h1 (not_lt.2 h4)

theorem mem_place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) (x : X.K) : x ∈ place X hτ ↔ 0 ≤ ord X τ x := Iff.rfl

theorem exists_place {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 →
      ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  refine ⟨place X hτ, ⟨fun c => ord_const X hτ c, ?_⟩, fun x hx φ hφ => ?_⟩
  · obtain ⟨φ, h, hφ⟩ := X.j_hol
    rw [mem_place, ord_eq X hτ h]
    exact (hφ.analyticOnNhd isOpen_Hs τ hτ).meromorphicOrderAt_nonneg
  · have h0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have h1 : 0 ≤ ord X τ x := (mem_place X hτ x).1 (((place X hτ).valuation_le_one_iff x).1 hx.le)
    have h2 : 0 ≤ ord X τ x⁻¹ := (mem_place X hτ _).1 (((place X hτ).valuation_le_one_iff _).1
      (by rw [map_inv₀, hx, inv_one]))
    have h3 := ord_add_ord_inv X hτ h0
    rw [← ord_eq X hτ hφ]
    refine le_antisymm ?_ h1
    calc ord X τ x = ord X τ x + 0 := (add_zero _).symm
      _ ≤ ord X τ x + ord X τ x⁻¹ := by gcongr
      _ = 0 := h3

end GlobalTheory.KZ.ValAt
