import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStableStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ringEquiv_eval_eq_eval_map {σ : Type} (e : ℂ ≃+* ℂ) (x : σ → ℂ)
    (p : MvPolynomial σ ℂ) :
    e (MvPolynomial.eval x p) =
      MvPolynomial.eval (fun i => e (x i)) (MvPolynomial.map (e : ℂ →+* ℂ) p) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  exact MvPolynomial.hom_eval₂ p (RingHom.id ℂ) (e : ℂ →+* ℂ) x

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ev_eq_evC_map_algebraMap {ι : Type} (p : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.ev p g =
      _root_.GlobalTheory.ClassFin.evC (MvPolynomial.map (algebraMap ℚ ℂ) p) g := by
  unfold _root_.GlobalTheory.ClassFin.ev _root_.GlobalTheory.ClassFin.evC
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma mem_span_rational_of_vanishing {ι : Type} (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) :
    f ∈ Submodule.span ℂ {w | ∃ p ∈ _root_.GlobalTheory.ClassFin.vanI Γ,
      MvPolynomial.map (algebraMap ℚ ℂ) p = w} := by
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {w | ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC w g = 0}
      add_mem' := fun {a b} ha hb g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, map_add] at *
        rw [ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by simp [_root_.GlobalTheory.ClassFin.evC]
      smul_mem' := fun c w hw g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, Set.mem_setOf_eq] at *
        rw [MvPolynomial.smul_eval, hw g hg, mul_zero] }
  have hstable : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr w' k =
        σ ((MvPolynomial.basisMonomials (ι × ι) ℂ).repr w k) := by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, fun g hg => ?_, fun k => MvPolynomial.coeff_map _ _ _⟩
    have h := hw (g.map σ.symm) (hΓ σ.symm g hg)
    have h2 := ringEquiv_eval_eq_eval_map σ (fun ij => (g.map σ.symm) ij.1 ij.2) w
    simp only [_root_.GlobalTheory.ClassFin.evC] at h ⊢
    rw [h, map_zero] at h2
    simpa [Matrix.map_apply] using h2.symm
  have hle := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ)
    W hstable
  refine Submodule.span_mono ?_ (hle hf)
  rintro w ⟨hwW, hrat⟩
  have hrange : w ∈ Set.range (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    obtain ⟨q, hq⟩ := hrat n
    exact ⟨q, hq.symm⟩
  obtain ⟨p, rfl⟩ := hrange
  refine ⟨p, fun g hg => ?_, rfl⟩
  rw [ev_eq_evC_map_algebraMap]
  exact hwW g hg

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) →
    ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) →
    ∀ y ∈ _root_.GlobalTheory.ClassFin.pts Γ ℂ, _root_.GlobalTheory.ClassFin.evC f y = 0 := by
  intro ι _ _ Γ hΓ f hf y hy
  have hspan := mem_span_rational_of_vanishing Γ hΓ f hf
  clear hf
  induction hspan using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    rw [← ev_eq_evC_map_algebraMap]
    exact hy p hp
  | zero => simp [_root_.GlobalTheory.ClassFin.evC]
  | add a b _ _ ha hb =>
    simp only [_root_.GlobalTheory.ClassFin.evC, map_add] at *
    rw [ha, hb, add_zero]
  | smul c w _ hw =>
    simp only [_root_.GlobalTheory.ClassFin.evC] at *
    rw [MvPolynomial.smul_eval, hw, mul_zero]

end GlobalTheory.ClassFin
