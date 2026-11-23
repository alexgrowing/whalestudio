import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real

namespace GlobalTheory.Mem.Lift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def dH (ρ : V → B →L[ℂ] B) (v : V) (f : B) : B := fderiv ℝ (fun u => ρ u f) 0 v

def quad (ρ : V → B →L[ℂ] B) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) (f : B) : B :=
  ∑ i, c i • dH ρ (p i) (dH ρ (q i) f)

def IsQuadOf (om : V → V → ℝ) (X : V → V) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) : Prop :=
  ∀ (l : V →ₗ[ℝ] ℂ) (v : V),
    2 * π * I * ∑ i, c i * ((om (q i) v : ℂ) * l (p i) + (om (p i) v : ℂ) * l (q i)) = l (X v)

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_add_left (ρ : V → B →L[ℂ] B) (u v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (u + v) f =
      _root_.GlobalTheory.Mem.Lift.dH ρ u f + _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_add _ _ _

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_smul_left (ρ : V → B →L[ℂ] B) (r : ℝ) (v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (r • v) f = r • _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_smul _ _ _

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_add {ρ : V → B →L[ℂ] B} (v : V) {f g : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) (hg : _root_.GlobalTheory.RealWeil.Sm ρ g) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (f + g) =
      _root_.GlobalTheory.Mem.Lift.dH ρ v f + _root_.GlobalTheory.Mem.Lift.dH ρ v g := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hg' : DifferentiableAt ℝ (fun u => ρ u g) 0 :=
    (ContDiff.differentiable hg (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_add]
  rw [(hf'.hasFDerivAt.fun_add hg'.hasFDerivAt).fderiv]
  rfl

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in
theorem _root_.GlobalTheory.Mem.Lift.dH_smul {ρ : V → B →L[ℂ] B} (v : V) (a : ℂ) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (a • f) = a • _root_.GlobalTheory.Mem.Lift.dH ρ v f := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_smul]
  rw [(hf'.hasFDerivAt.fun_const_smul a).fderiv]
  rfl

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in

theorem _root_.GlobalTheory.Mem.Lift.hasDerivAt_dH {ρ : V → B →L[ℂ] B} (v : V) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (_root_.GlobalTheory.Mem.Lift.dH ρ v f) 0 := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

open MeasureTheory Complex Matrix in
open scoped ContDiff Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B] in

theorem _root_.GlobalTheory.Mem.Lift.dH_comm {ρ : V → B →L[ℂ] B} (A : B →L[ℂ] B)
    (hA : ∀ v f, A (ρ v f) = ρ v (A f)) {f : B} (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.RealWeil.Sm ρ (A f) ∧
      ∀ v, _root_.GlobalTheory.Mem.Lift.dH ρ v (A f) = A (_root_.GlobalTheory.Mem.Lift.dH ρ v f) := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hfun : (fun u => ρ u (A f)) = fun u => (A.restrictScalars ℝ) (ρ u f) := by
    funext u
    simp [hA]
  refine ⟨?_, fun v => ?_⟩
  · unfold _root_.GlobalTheory.RealWeil.Sm
    rw [hfun]
    exact (A.restrictScalars ℝ).contDiff.comp hf
  · unfold _root_.GlobalTheory.Mem.Lift.dH
    have h : HasFDerivAt (fun u => (A.restrictScalars ℝ) (ρ u f))
        ((A.restrictScalars ℝ).comp (fderiv ℝ (fun u => ρ u f) 0)) 0 :=
      (A.restrictScalars ℝ).hasFDerivAt.comp (0 : V) hf'.hasFDerivAt
    rw [hfun, h.fderiv]
    rfl

def smS (ρ : V → B →L[ℂ] B) : Submodule ℂ B where
  carrier := {f | Sm ρ f}
  add_mem' := fun hf hg => by simpa only [Set.mem_setOf_eq, Sm, map_add] using ContDiff.add (show ContDiff ℝ ∞ _ from hf) (show ContDiff ℝ ∞ _ from hg)
  zero_mem' := by simpa only [Set.mem_setOf_eq, Sm, map_zero] using contDiff_const
  smul_mem' := fun a _ hf => by simpa only [Set.mem_setOf_eq, Sm, map_smul] using ContDiff.const_smul a (show ContDiff ℝ ∞ _ from hf)

end General

section Coord

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def xOp (ρ : (ι → ℂ) → B →L[ℂ] B) (k : ι) (f : B) : B :=
  dH ρ (Pi.single k 1) f - I • dH ρ (I • Pi.single k 1) f

def dOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (l : ι) (f : B) : B :=
  (-(1 / (4 * π)) : ℂ) • (dH ρ (H⁻¹ *ᵥ Pi.single l 1) f + I • dH ρ (I • H⁻¹ *ᵥ Pi.single l 1) f)

def nOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H X : Matrix ι ι ℂ) (f : B) : B := ∑ k, ∑ l, X k l • xOp ρ k (dOp ρ H l f)

end Coord

def IsCCR {A : Type} [Ring A] {κ : Type} [DecidableEq κ] (x d : κ → A) : Prop :=
  (∀ k l, x k * x l = x l * x k) ∧ (∀ k l, d k * d l = d l * d k) ∧
    ∀ k l, d l * x k - x k * d l = if k = l then 1 else 0

end GlobalTheory.Mem.Lift

end
