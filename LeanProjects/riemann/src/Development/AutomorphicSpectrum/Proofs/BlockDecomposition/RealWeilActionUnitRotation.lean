import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasTemperateGrowthConjPow
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.RealCircle

theorem normSq_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (z : ℂ) :
    Complex.normSq (z * u) = Complex.normSq z := by
  rw [map_mul, Complex.normSq_eq_norm_sq u, hu]
  simp

theorem integral_volC_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (F : ℂ → ℂ) :
    ∫ w, F (w * u) ∂volC = ∫ w, F w ∂volC := by
  have hm : MeasurePreserving (rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle)) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have h := hm.integral_comp
    (rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle)).toHomeomorph.measurableEmbedding F
  have e : ∀ w : ℂ, (rotation (⟨u, mem_sphere_zero_iff_norm.2 hu⟩ : Circle)) w = u * w := fun w => rfl
  simp only [e] at h
  unfold volC
  rw [integral_smul_measure, integral_smul_measure]
  simp only [mul_comm _ u]
  rw [h]

theorem rWR_circle (a b c d : ℝ) {Φ : ℂ → ℂ} {u k : ℂ} (hu : ‖u‖ = 1)
    (hΦ : ∀ z, Φ (z * u) = k * Φ z) (x : ℂ) :
    rWR a b c d Φ (x * u) = k * rWR a b c d Φ x := by
  have hc : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  unfold rWR
  split_ifs with h0
  · rw [normSq_mul_unit hu, ← mul_assoc (a : ℂ) x u, hΦ]
    ring
  · rw [← integral_volC_mul_unit hu (fun w => Complex.exp (2 * Real.pi * Complex.I *
      (((a * Complex.normSq (x * u) + d * Complex.normSq w -
        2 * ((starRingEnd ℂ) (x * u) * w).re) / c : ℝ) : ℂ)) * Φ w)]
    have e : ∀ w : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq (x * u) + d * Complex.normSq (w * u) -
          2 * ((starRingEnd ℂ) (x * u) * (w * u)).re) / c : ℝ) : ℂ)) * Φ (w * u) =
        k * (Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq x + d * Complex.normSq w -
          2 * ((starRingEnd ℂ) x * w).re) / c : ℝ) : ℂ)) * Φ w) := by
      intro w
      have e1 : (starRingEnd ℂ) (x * u) * (w * u) = (starRingEnd ℂ) x * w := by
        rw [map_mul]
        linear_combination ((starRingEnd ℂ) x * w) * hc
      rw [e1, normSq_mul_unit hu, normSq_mul_unit hu, hΦ]
      ring
    simp_rw [e]
    rw [integral_const_mul]
    ring

theorem piRc_circle (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (x u : ℂ) (hu : ‖u‖ = 1) :
    piRc (chC n (Complex.I * t)) g (PhiInf n) (x * u) =
      u ^ (-n) * piRc (chC n (Complex.I * t)) g (PhiInf n) x := by
  unfold piRc
  split_ifs with h
  · rw [rWR_circle _ _ _ _ hu (k := u ^ (-n)) (fun z => by
      rw [mul_right_comm z u, (GlobalTheory.CompanionTheory.PhiInfIso.phiIso n).2 _ _ hu]) x]
    ring
  · simp

theorem main : ∀ (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (x u : ℂ), ‖u‖ = 1 →
    piRc (chC n (Complex.I * t)) g (PhiInf n) (x * u) =
      u ^ (-n) * piRc (chC n (Complex.I * t)) g (PhiInf n) x :=
  fun n t g x u hu => piRc_circle n t g x u hu

end GlobalTheory.CompanionTheory.FexTheta.RealCircle
