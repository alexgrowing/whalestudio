import Mathlib

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E'']

def holSub (W : Opens E) : Subalgebra ℂ (W → ℂ) where
  carrier := {f | ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f p = F p}
  mul_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p * G p, hF.mul hG, fun p ↦ by simp [e, e']⟩
  add_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p + G p, hF.add hG, fun p ↦ by simp [e, e']⟩
  algebraMap_mem' c := ⟨fun _ ↦ c, analyticOnNhd_const, fun _ ↦ rfl⟩

abbrev Hol (W : Opens E) : Type := holSub W

namespace Hol

variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''}

open Classical in

def fn (f : Hol W) (p : E) : ℂ := if h : p ∈ W then f.1 ⟨p, h⟩ else 0

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_of_mem (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (h : p ∈ W) :
    f.fn p = f.1 ⟨p, h⟩ := by
  simp [_root_.GlobalTheory.AnPer.Hol.fn, h]

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.ext_fn {f g : _root_.GlobalTheory.AnPer.Hol W}
    (h : ∀ p ∈ W, f.fn p = g.fn p) : f = g := by
  refine Subtype.ext (funext fun p ↦ ?_)
  have hp := h p p.2
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f p.2, _root_.GlobalTheory.AnPer.Hol.fn_of_mem g p.2] at hp
  exact hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.analytic (f : _root_.GlobalTheory.AnPer.Hol W) :
    AnalyticOnNhd ℂ f.fn W := by
  obtain ⟨F, hF, e⟩ : ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f.1 p = F p := f.2
  intro p hp
  refine (hF p hp).congr ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hq, e]

def mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) : Hol W := ⟨fun p ↦ F p, F, h, fun _ ↦ rfl⟩

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.mk F h).fn p = F p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def ev (p : E) (hp : p ∈ W) : Hol W →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : W ↦ ℂ) ⟨p, hp⟩).comp (holSub W).val

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.ev_apply (p : E) (hp : p ∈ W) (f : _root_.GlobalTheory.AnPer.Hol W) :
    _root_.GlobalTheory.AnPer.Hol.ev p hp f = f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_add (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f + g).fn p = f.fn p + g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_mul (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f * g).fn p = f.fn p * g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_smul (c : ℂ) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (c • f).fn p = c * f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_algebraMap (c : ℂ) {p : E} (hp : p ∈ W) :
    (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol W) c).fn p = c := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W) : Hol W →ₐ[ℂ] Hol W' where
  toFun f := ⟨fun p ↦ f.1 ⟨Φ p, h p p.2⟩, fun p ↦ f.fn (Φ p), f.analytic.comp hΦ h,
    fun p ↦ (fn_of_mem f _).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W)
    (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f).fn p = f.fn (Φ p) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  exact (_root_.GlobalTheory.AnPer.Hol.fn_of_mem f (h p hp)).symm

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (f : _root_.GlobalTheory.AnPer.Hol W) {F : E → ℂ}
    (e : ∀ q ∈ W, f.fn q = F q) {p : E} (hp : p ∈ W) :
    fderiv ℂ f.fn p = fderiv ℂ F p := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq using e q hq

def derFun (v : E) (f : Hol W) : Hol W :=
  mk (fun p ↦ fderiv ℂ f.fn p v) fun p hp ↦
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (f.analytic p hp).fderiv

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_derFun (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.derFun v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hp

def der (v : E) : Derivation ℂ (Hol W) (Hol W) :=
  Derivation.mk'
    { toFun := derFun v
      map_add' f g := ext_fn fun p hp ↦ by
        rw [fn_add _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (f + g) (F := fun q ↦ f.fn q + g.fn q) (fun q hq ↦ fn_add f g hq) hp,
          fderiv_fun_add (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
        rfl
      map_smul' c f := ext_fn fun p hp ↦ by
        rw [RingHom.id_apply, fn_smul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (c • f) (F := fun q ↦ c * f.fn q) (fun q hq ↦ fn_smul c f hq) hp,
          fderiv_const_mul (f.analytic p hp).differentiableAt]
        rfl }
    fun f g ↦ ext_fn fun p hp ↦ by
      change (derFun v (f * g)).fn p = (f * derFun v g + g * derFun v f).fn p
      rw [fn_add _ _ hp, fn_mul _ _ hp, fn_mul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
        fderiv_fn_congr (f * g) (F := fun q ↦ f.fn q * g.fn q) (fun q hq ↦ fn_mul f g hq) hp,
        fderiv_fun_mul (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
      rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_der (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.der v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_derFun v f hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_der_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W')
    (h : ∀ p ∈ W', Φ p ∈ W) (v : E') (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.der v (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f)).fn p =
      fderiv ℂ f.fn (Φ p) (fderiv ℂ Φ p v) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_der v _ hp,
    _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr _ (F := f.fn ∘ Φ)
      (fun q hq ↦ _root_.GlobalTheory.AnPer.Hol.fn_comap Φ hΦ h f hq) hp,
    fderiv_comp p (f.analytic (Φ p) (h p hp)).differentiableAt
      (hΦ p hp).differentiableAt]
  rfl

end Hol

end GlobalTheory.AnPer
