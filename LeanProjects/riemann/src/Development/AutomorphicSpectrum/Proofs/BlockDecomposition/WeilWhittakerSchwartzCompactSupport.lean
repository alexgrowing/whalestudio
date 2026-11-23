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

namespace GlobalTheory.CompanionTheory.WeilRd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rW_const_mul (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d : F)
    (k : ℂ) (Φ : E → ℂ) (z : E) :
    GL2LocalData.rW χ σ μE lam a b c d (fun x => k * Φ x) z = k * GL2LocalData.rW χ σ μE lam a b c d Φ z := by
  unfold GL2LocalData.rW
  split_ifs with h
  · ring
  · have : (fun u => (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * (k * Φ u))
        = fun u => k * ((χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * Φ u) := by
      funext u; ring
    rw [this, MeasureTheory.integral_const_mul]
    ring

end GlobalTheory.CompanionTheory.WeilRd

open GlobalTheory.CompanionTheory.WeilRd in

theorem GlobalTheory.CompanionTheory.WeilRd.main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → ∀ (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ (s : Eˣ) (g : GL (Fin 2) F), GL2LocalData.Wc χ σ μ lam c Φ (g * dg2 (Units.map (Algebra.norm F : E →* F) s) 1) = ((c s : ℂˣ) : ℂ) * (((modulus (Algebra.norm F (s : E)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * GL2LocalData.Wc χ σ μ lam c (fun z => Φ (z * (s : E))) g := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hΦ s g
  set m : Fˣ := Units.map (Algebra.norm F : E →* F) s with hm
  have hmv : (m : F) = Algebra.norm F (s : E) := rfl
  have hm0 : (m : F) ≠ 0 := m.ne_zero
  have e00 : (g * dg2 m 1).val 0 0 = g.val 0 0 * m := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * dg2 m 1).val 0 1 = g.val 0 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * dg2 m 1).val 1 0 = g.val 1 0 * m := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * dg2 m 1).val 1 1 = g.val 1 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have edet : ((g * dg2 m 1).val).det = (g.val).det * m := by
    simp [dg2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hΔ : (g.val).det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom)
    exact this.ne_zero
  have hiff : (∃ t : Eˣ, Algebra.norm F (t : E) = ((g * dg2 m 1).val).det) ↔
      ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := by
    rw [edet]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t * s⁻¹, ?_⟩
      have h1 : Algebra.norm F ((s⁻¹ : Eˣ) : E) * m = 1 := by
        rw [hmv, ← map_mul, Units.inv_mul, map_one]
      rw [Units.val_mul, map_mul, ht, mul_assoc, mul_comm (m : F), h1, mul_one]
    · rintro ⟨t, ht⟩
      exact ⟨t * s, by rw [Units.val_mul, map_mul, ht, hmv]⟩
  unfold GL2LocalData.Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' := hiff.2 h
    rw [dif_pos h', dif_pos h]
    set t := h.choose with ht
    set t' := h'.choose with ht'
    have nt : Algebra.norm F (t : E) = (g.val).det := h.choose_spec
    have nt' : Algebra.norm F (t' : E) = (g.val).det * m := by
      rw [← edet]; exact h'.choose_spec
    set u : Eˣ := t' * (t * s)⁻¹ with hu
    have hts : t' = (t * s) * u := by rw [hu, mul_comm, inv_mul_cancel_right]
    have nts : Algebra.norm F ((t * s : Eˣ) : E) = (g.val).det * m := by
      rw [Units.val_mul, map_mul, nt, hmv]
    have nu : Algebra.norm F (u : E) = 1 := by
      have h2 : Algebra.norm F (t' : E) = Algebra.norm F ((t * s : Eˣ) : E) * Algebra.norm F (u : E) := by
        conv_lhs => rw [hts]
        rw [Units.val_mul, map_mul]
      rw [nt', nts] at h2
      have hne : (g.val).det * (m : F) ≠ 0 := mul_ne_zero hΔ hm0
      exact (mul_eq_left₀ hne).1 h2.symm
    have hfun : (fun x => Φ (x * (t' : E))) =
        fun x => (((c u)⁻¹ : ℂˣ) : ℂ) * (fun z => Φ (z * (s : E))) (x * (t : E)) := by
      funext x
      have := hΦ.2.2 u nu (x * (t : E) * (s : E))
      rw [hts]
      simp only [Units.val_mul]
      rw [← this]
      congr 1
      ring
    have a1 : (g * dg2 m 1).val 0 0 / ((g * dg2 m 1).val).det = g.val 0 0 / (g.val).det := by
      rw [e00, edet]; field_simp
    have a2 : (g * dg2 m 1).val 1 0 / ((g * dg2 m 1).val).det = g.val 1 0 / (g.val).det := by
      rw [e10, edet]; field_simp
    rw [a1, a2, e01, e11, edet, hfun, rW_const_mul]
    have hc : ((c t' : ℂˣ) : ℂ) = ((c t : ℂˣ) : ℂ) * ((c s : ℂˣ) : ℂ) * ((c u : ℂˣ) : ℂ) := by
      rw [hts]; simp [map_mul]
    have hmod : (((modulus ((g.val).det * (m : F)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
        ((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((modulus (m : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
      rw [modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [hc, hmod, ← hmv]
    have hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (((c t : ℂˣ) : ℂ) * ((c s : ℂˣ) : ℂ) * ((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((modulus (m : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) * GL2LocalData.rW χ σ μ lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => (fun z => Φ (z * (s : E))) (x * (t : E))) 1) * hcu
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * dg2 m 1).val).det := fun q => h (hiff.1 q)
    rw [dif_neg h', dif_neg h, mul_zero]
