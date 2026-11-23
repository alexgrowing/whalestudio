import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic

noncomputable section

namespace PhScale

theorem eisensteinSum_scaleLattice (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    eisensteinSum (scaleLattice c Λ) n = (c ^ n)⁻¹ * eisensteinSum Λ n := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ c) := fun x y h ↦ mul_left_cancel₀ hc h
  let e := Submodule.equivMapOfInjective _ hinj Λ
  unfold eisensteinSum scaleLattice
  refine (e.toEquiv.tsum_eq (fun l ↦ ((l : ℂ) ^ n)⁻¹)).symm.trans ?_
  rw [← tsum_mul_left]
  congr 1
  funext x
  simp [e, mul_pow]
  ring

theorem latticeDiscr_scaleLattice (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) :
    latticeDiscr (scaleLattice c Λ) = (c ^ 12)⁻¹ * latticeDiscr Λ := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scaleLattice Λ hc]
  ring

def scalePair (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have := L.indep
    rw [LinearIndependent.pair_iff] at this ⊢
    intro s t hst
    apply this s t
    have hst' : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.1 hst').resolve_left hc

theorem lattice_scalePair (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) :
    (scalePair L hc).lattice = scaleLattice c L.lattice := by
  simp [PeriodPair.lattice, scaleLattice, Submodule.map_span, Set.image_pair, scalePair]

theorem det_mulLeft (c : ℂ) : LinearMap.det (LinearMap.mulLeft ℝ c) = ‖c‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
  rfl

theorem latticeArea_scaleLattice (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) :
    latticeArea (scaleLattice c L.lattice) = ‖c‖ ^ 2 * latticeArea L.lattice := by
  rw [← lattice_scalePair L hc]
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (scalePair L hc).latticeBasis Complex.basisOneI,
    ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI]
  have hv : ((↑) ∘ (scalePair L hc).latticeBasis : Fin 2 → ℂ) =
      (LinearMap.mulLeft ℝ c) ∘ ((↑) ∘ L.latticeBasis) := by
    funext i
    fin_cases i <;> simp <;> rfl
  rw [hv, Module.Basis.det_comp, abs_mul, det_mulLeft, abs_of_nonneg (by positivity), mul_assoc]

theorem proof : PhScale.Statement := by
  intro L c hc
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hA : 0 < latticeArea L.lattice := ZLattice.covolume_pos _ _
  have hAπ : latticeArea L.lattice / Real.pi ≠ 0 := (div_pos hA Real.pi_pos).ne'
  have hD : ‖latticeDiscr L.lattice‖ ≠ 0 := by
    rw [latticeDiscr_lattice]
    exact norm_ne_zero_iff.2 (discr_ne_zero L)
  unfold logPeriod
  rw [latticeArea_scaleLattice L hc, latticeDiscr_scaleLattice _ hc, norm_mul, norm_inv, norm_pow,
    mul_div_assoc, Real.log_mul (pow_ne_zero _ hn) hAπ,
    Real.log_mul (inv_ne_zero (pow_ne_zero _ hn)) hD, Real.log_inv, Real.log_pow, Real.log_pow]
  push_cast
  ring

end PhScale

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
