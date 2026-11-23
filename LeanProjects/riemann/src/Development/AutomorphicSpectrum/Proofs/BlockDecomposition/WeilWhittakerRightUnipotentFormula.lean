import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WinertRn

variable {F : Type} [Field F]

theorem det_mul_right_unipotent (x : F) (g : GL (Fin 2) F) : ((g * uni2 x).val).det = (g.val).det := by
  simp [uni2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_upper_left (x : F) (g : GL (Fin 2) F) : (g * uni2 x).val 0 0 = g.val 0 0 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_lower_left (x : F) (g : GL (Fin 2) F) : (g * uni2 x).val 1 0 = g.val 1 0 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_upper_right (x : F) (g : GL (Fin 2) F) :
    (g * uni2 x).val 0 1 = g.val 0 0 * x + g.val 0 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_right_unipotent_lower_right (x : F) (g : GL (Fin 2) F) :
    (g * uni2 x).val 1 1 = g.val 1 0 * x + g.val 1 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem rW_shift {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {E : Type} [Field E] [TopologicalSpace E] [MeasurableSpace E] [Algebra F E]
    (hE : Module.finrank F E = 2) (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ)
    (Φ : E → ℂ) (x A B C D Δ : F) (hΔ : Δ ≠ 0) (t : E) (ht : Algebra.norm F t = Δ) :
    GL2LocalData.rW χ σ μ lam (A / Δ) (A * x + B) (C / Δ) (C * x + D) (fun y => Φ (y * t)) 1 =
      GL2LocalData.rW χ σ μ lam (A / Δ) B (C / Δ) D
        (fun y => (χ (x * Algebra.norm F (y * t)) : ℂ) * Φ (y * t)) 1 := by
  unfold GL2LocalData.rW
  by_cases hc : C / Δ = 0
  · rw [if_pos hc, if_pos hc]
    have hN : Algebra.norm F (algebraMap F E (A / Δ) * 1 * t) = (A / Δ) ^ 2 * Δ := by
      rw [mul_one, map_mul, Algebra.norm_algebraMap, hE, ht]
    have hadd : A / Δ * (A * x + B) * Algebra.norm F (1 : E) =
        A / Δ * B * Algebra.norm F (1 : E) + x * Algebra.norm F (algebraMap F E (A / Δ) * 1 * t) := by
      rw [hN, map_one]
      field_simp
      ring
    rw [hadd, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul]
    ring
  · rw [if_neg hc, if_neg hc]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hC : C ≠ 0 := fun h => hc (by simp [h])
    have hN : Algebra.norm F (u * t) = Algebra.norm F u * Δ := by rw [map_mul, ht]
    have hadd : (A / Δ * Algebra.norm F (1 : E) + (C * x + D) * Algebra.norm F u -
          Algebra.trace F E (σ 1 * u)) / (C / Δ) =
        (A / Δ * Algebra.norm F (1 : E) + D * Algebra.norm F u -
          Algebra.trace F E (σ 1 * u)) / (C / Δ) + x * Algebra.norm F (u * t) := by
      rw [hN]
      field_simp
      ring
    simp only []
    rw [hadd, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul]
    ring

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * uni2 x) = GL2LocalData.Wc χ σ μ lam c (fun z => (χ (x * Algebra.norm F z) : ℂ) * Φ z) g := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hE χ σ μ lam c Φ x g
  unfold GL2LocalData.Wc
  rw [det_mul_right_unipotent, mul_right_unipotent_upper_left, mul_right_unipotent_lower_left, mul_right_unipotent_upper_right, mul_right_unipotent_lower_right]
  split_ifs with h
  · have hΔ : (g.val).det ≠ 0 := by
      have := g.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
      exact this.ne_zero
    rw [rW_shift hE χ σ μ lam Φ x _ _ _ _ _ hΔ (h.choose : E) h.choose_spec]
  · rfl

end GlobalTheory.CompanionTheory.WinertRn
