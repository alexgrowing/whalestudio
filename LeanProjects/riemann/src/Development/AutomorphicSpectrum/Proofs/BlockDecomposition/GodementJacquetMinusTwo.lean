import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive

noncomputable section

open Classical

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.GL2Coordinates

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem modulus_neg' (x : F) : modulus (-x) = modulus x := by
  have h1 : modulus (-1 : F) = 1 := by
    have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
      rw [← modulus_mul]; simp
    have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  rw [show -x = (-1) * x by ring, modulus_mul, h1, one_mul]

section Core

variable (ν : Measure F) [ν.IsAddHaarMeasure]

theorem lint_affine {a : F} (ha : a ≠ 0) (b : F) (g : F → ℝ≥0∞) :
    ∫⁻ x, g x ∂ν = (modulus a : ℝ≥0∞) * ∫⁻ x, g (a * x + b) ∂ν := by
  rw [lintegral_comp_mul_left ν ha (fun x => g (x + b)), lintegral_add_right_eq_self g b,
    ← mul_assoc, ENNReal.mul_inv_cancel (by simpa using modulus_ne_zero ha) ENNReal.coe_ne_top,
    one_mul]

theorem fibre {A B : F} (hB : B ≠ 0) (G : F → F → ℝ≥0∞) (hG : Measurable (Function.uncurry G))
    (h0 : ∀ C D, A * D - B * C = 0 → G C D = 0) :
    ∫⁻ C, ∫⁻ D, G C D ∂ν ∂ν = ∫⁻ y, ∫⁻ t, (if y = 0 then 0 else
      (((modulus y)⁻¹ : ℝ≥0) : ℝ≥0∞) * G (-(t * A / y) - y / B) (-(t * B / y))) ∂ν ∂ν := by
  have hBn : modulus B ≠ 0 := modulus_ne_zero hB
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have e1 : ∀ D, ∫⁻ C, G C D ∂ν = (((modulus B)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ y, G ((A * D - y) / B) D ∂ν := by
    intro D
    rw [lint_affine ν (a := -B⁻¹) (neg_ne_zero.2 (inv_ne_zero hB)) (A * D / B) (fun C => G C D),
      modulus_neg', modulus_inv]
    congr 2
    funext y
    congr 1
    field_simp
    ring
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hm : Measurable (Function.uncurry fun (D y : F) => G ((A * D - y) / B) D) :=
    hG.comp (f := fun p : F × F => ((A * p.1 - p.2) / B, p.1)) (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun y => ?_
  by_cases hy : y = 0
  · subst hy
    have : ∀ D, G (A * D / B) D = 0 := fun D => h0 _ _ (by field_simp; ring)
    simp [this]
  · simp only [hy, if_false]
    rw [lint_affine ν (a := -(B / y)) (neg_ne_zero.2 (div_ne_zero hB hy)) 0
      (fun D => G ((A * D - y) / B) D), modulus_neg', ← mul_assoc, ← ENNReal.coe_mul,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    have hc : (modulus B)⁻¹ * modulus (B / y) = (modulus y)⁻¹ := by
      rw [div_eq_mul_inv, modulus_mul, modulus_inv, ← mul_assoc, inv_mul_cancel₀ hBn, one_mul]
    rw [hc]
    refine lintegral_congr fun t => ?_
    congr 2
    · field_simp
      ring
    · field_simp
      ring

theorem swap4 (P : F → F → F → F → ℝ≥0∞)
    (hP : Measurable fun p : F × F × F × F => P p.1 p.2.1 p.2.2.1 p.2.2.2) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, P a b c d ∂ν ∂ν ∂ν ∂ν = ∫⁻ c, ∫⁻ d, ∫⁻ a, ∫⁻ b, P a b c d ∂ν ∂ν ∂ν ∂ν := by
  let R : F × F → F × F → ℝ≥0∞ := fun p q => P p.1 p.2 q.1 q.2
  have hR : Measurable (Function.uncurry R) :=
    hP.comp (f := fun z : (F × F) × (F × F) => (z.1.1, z.1.2, z.2.1, z.2.2)) (by fun_prop)
  have hR1 : ∀ p, Measurable (R p) := fun p => hR.of_uncurry_left
  have hR2 : ∀ q, Measurable fun p => R p q := fun q => hR.of_uncurry_right
  calc ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, P a b c d ∂ν ∂ν ∂ν ∂ν
      = ∫⁻ a, ∫⁻ b, ∫⁻ q, R (a, b) q ∂ν.prod ν ∂ν ∂ν := by
        refine lintegral_congr fun a => lintegral_congr fun b => ?_
        rw [lintegral_prod _ (hR1 (a, b)).aemeasurable]
    _ = ∫⁻ p, ∫⁻ q, R p q ∂ν.prod ν ∂ν.prod ν := by
        exact (lintegral_prod (fun p => ∫⁻ q, R p q ∂ν.prod ν) (Measurable.aemeasurable hR.lintegral_prod_right')).symm
    _ = ∫⁻ q, ∫⁻ p, R p q ∂ν.prod ν ∂ν.prod ν := lintegral_lintegral_swap hR.aemeasurable
    _ = ∫⁻ c, ∫⁻ d, ∫⁻ p, R p (c, d) ∂ν.prod ν ∂ν ∂ν := by
        exact lintegral_prod (fun q => ∫⁻ p, R p q ∂ν.prod ν) (Measurable.aemeasurable hR.lintegral_prod_left')
    _ = ∫⁻ c, ∫⁻ d, ∫⁻ a, ∫⁻ b, P a b c d ∂ν ∂ν ∂ν ∂ν := by
        refine lintegral_congr fun c => lintegral_congr fun d => ?_
        rw [lintegral_prod _ (hR2 (c, d)).aemeasurable]

end Core

section Core2

variable (ν : Measure F) [ν.IsAddHaarMeasure]

theorem null0 : ν {0} = 0 := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq F 1
  have h := addHaar_smul ν hc ({0} : Set F)
  rw [Set.smul_set_singleton, smul_zero] at h
  have hm : modulus c ≠ 1 := by
    intro h1
    have := (modulus_eq_one_iff.1 h1).2
    omega
  have ht : ν {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  by_contra h0
  have := (ENNReal.mul_eq_right h0 ht).1 h.symm
  exact hm (by exact_mod_cast this)

def Pc (K : F × F × F × F → ℝ≥0∞) (A B y t : F) : ℝ≥0∞ :=
  if B = 0 ∨ y = 0 then 0 else
    (((modulus y)⁻¹ : ℝ≥0) : ℝ≥0∞) * K (A, B, -(t * A / y) - y / B, -(t * B / y))

def Qc (K : F × F × F × F → ℝ≥0∞) (u v t y : F) : ℝ≥0∞ :=
  if v = 0 ∨ y = 0 then 0 else
    (modulus y : ℝ≥0∞) * K (y * u, y * v, -(t * u) - 1 / v, -(t * v))

theorem measurable_Pc {K : F × F × F × F → ℝ≥0∞} (hK : Measurable K) :
    Measurable fun p : F × F × F × F => Pc K p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hm : Measurable fun x : F => (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    (measurable_modulus.inv).coe_nnreal_ennreal
  refine Measurable.ite ?_ measurable_const ?_
  · exact ((measurableSet_singleton (0 : F)).preimage (by fun_prop : Measurable fun p : F × F × F × F => p.2.1)).union
      ((measurableSet_singleton (0 : F)).preimage (by fun_prop : Measurable fun p : F × F × F × F => p.2.2.1))
  · exact (hm.comp (by fun_prop)).mul (hK.comp (by fun_prop))

theorem measurable_Qc {K : F × F × F × F → ℝ≥0∞} (hK : Measurable K) :
    Measurable fun p : F × F × F × F => Qc K p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hm : Measurable fun x : F => ((modulus x : ℝ≥0) : ℝ≥0∞) :=
    measurable_modulus.coe_nnreal_ennreal
  refine Measurable.ite ?_ measurable_const ?_
  · exact ((measurableSet_singleton (0 : F)).preimage (by fun_prop : Measurable fun p : F × F × F × F => p.2.1)).union
      ((measurableSet_singleton (0 : F)).preimage (by fun_prop : Measurable fun p : F × F × F × F => p.2.2.2))
  · exact (hm.comp (by fun_prop)).mul (hK.comp (by fun_prop))

theorem scale_Pc (K : F × F × F × F → ℝ≥0∞) (y t : F) :
    ∫⁻ A, ∫⁻ B, Pc K A B y t ∂ν ∂ν = ∫⁻ u, ∫⁻ v, Qc K u v t y ∂ν ∂ν := by
  by_cases hy : y = 0
  · simp [Pc, Qc, hy]
  have hnn : modulus y ≠ 0 := modulus_ne_zero hy
  have h1 : (modulus y : ℝ≥0∞) * (((modulus y)⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, mul_inv_cancel₀ hnn, ENNReal.coe_one]
  rw [lint_affine ν hy 0 (fun A => ∫⁻ B, Pc K A B y t ∂ν)]
  simp only [add_zero]
  have e : ∀ u, ∫⁻ B, Pc K (y * u) B y t ∂ν = ∫⁻ v, (modulus y : ℝ≥0∞) * Pc K (y * u) (y * v) y t ∂ν := by
    intro u
    rw [lint_affine ν hy 0 (fun B => Pc K (y * u) B y t)]
    simp only [add_zero]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  simp_rw [e]
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun u => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun v => ?_
  by_cases hv : v = 0
  · simp [Pc, Qc, hv]
  have ha : ((y * u, y * v, -(t * (y * u) / y) - y / (y * v), -(t * (y * v) / y)) : F × F × F × F) =
      (y * u, y * v, -(t * u) - 1 / v, -(t * v)) := by
    simp only [Prod.mk.injEq, true_and]
    constructor
    · field_simp
    · field_simp
  rw [Pc, Qc, if_neg (by simp [hy, hv]), if_neg (by simp [hy, hv]), ha]
  congr 1
  rw [← mul_assoc, h1, one_mul]

theorem core (K : F × F × F × F → ℝ≥0∞) (hK : Measurable K)
    (h0 : ∀ A B C D, A * D - B * C = 0 → K (A, B, C, D) = 0) :
    ∫⁻ A, ∫⁻ B, ∫⁻ C, ∫⁻ D, K (A, B, C, D) ∂ν ∂ν ∂ν ∂ν =
      ∫⁻ u, ∫⁻ v, ∫⁻ t, ∫⁻ y, Qc K u v t y ∂ν ∂ν ∂ν ∂ν := by
  have hQ := measurable_Qc hK
  calc ∫⁻ A, ∫⁻ B, ∫⁻ C, ∫⁻ D, K (A, B, C, D) ∂ν ∂ν ∂ν ∂ν
      = ∫⁻ A, ∫⁻ B, ∫⁻ y, ∫⁻ t, Pc K A B y t ∂ν ∂ν ∂ν ∂ν := by
        refine lintegral_congr fun A => lintegral_congr_ae ?_
        filter_upwards [compl_mem_ae_iff.2 (null0 ν)] with B hB
        have hB' : B ≠ 0 := hB
        rw [fibre ν hB' (fun C D => K (A, B, C, D))
          (hK.comp (f := fun p : F × F => (A, B, p.1, p.2)) (by fun_prop)) (fun C D h => h0 A B C D h)]
        refine lintegral_congr fun y => lintegral_congr fun t => ?_
        simp only [Pc, hB', false_or]
    _ = ∫⁻ y, ∫⁻ t, ∫⁻ A, ∫⁻ B, Pc K A B y t ∂ν ∂ν ∂ν ∂ν := swap4 ν (Pc K) (measurable_Pc hK)
    _ = ∫⁻ y, ∫⁻ t, ∫⁻ u, ∫⁻ v, Qc K u v t y ∂ν ∂ν ∂ν ∂ν :=
        lintegral_congr fun y => lintegral_congr fun t => scale_Pc ν K y t
    _ = ∫⁻ u, ∫⁻ v, ∫⁻ y, ∫⁻ t, Qc K u v t y ∂ν ∂ν ∂ν ∂ν :=
        swap4 ν (fun y t u v => Qc K u v t y)
          (hQ.comp (f := fun p : F × F × F × F => (p.2.2.1, p.2.2.2, p.2.1, p.1)) (by fun_prop))
    _ = ∫⁻ u, ∫⁻ v, ∫⁻ t, ∫⁻ y, Qc K u v t y ∂ν ∂ν ∂ν ∂ν := by
        refine lintegral_congr fun u => lintegral_congr fun v => ?_
        exact lintegral_lintegral_swap
          (hQ.comp (f := fun p : F × F => (u, v, p.2, p.1)) (by fun_prop)).aemeasurable

end Core2

def mat4 (p : F × F × F × F) : Fin 2 × Fin 2 → F :=
  fun ij => !![p.1, p.2.1; p.2.2.1, p.2.2.2] ij.1 ij.2

theorem measurable_entries_four : Measurable (mat4 (F := F)) := by
  refine measurable_pi_lambda _ fun ij => ?_
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [mat4] <;> fun_prop

theorem pi_eq_map (ν : Measure F) [ν.IsAddHaarMeasure] :
    (Measure.pi fun _ : Fin 2 × Fin 2 => ν) = (ν.prod (ν.prod (ν.prod ν))).map mat4 := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_entries_four (MeasurableSet.univ_pi hs)]
  have : mat4 ⁻¹' Set.univ.pi s = s (0, 0) ×ˢ s (0, 1) ×ˢ s (1, 0) ×ˢ s (1, 1) := by
    ext p
    simp [mat4, Set.mem_pi, Prod.forall, Fin.forall_fin_two, and_assoc]
  rw [this, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, mul_assoc]

theorem lint4 (ν : Measure F) [ν.IsAddHaarMeasure] {K : F × F × F × F → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p, K p ∂(ν.prod (ν.prod (ν.prod ν))) = ∫⁻ A, ∫⁻ B, ∫⁻ C, ∫⁻ D, K (A, B, C, D) ∂ν ∂ν ∂ν ∂ν := by
  rw [lintegral_prod _ hK.aemeasurable]
  refine lintegral_congr fun A => ?_
  have hA : Measurable fun p : F × F × F => K (A, p) := hK.comp (by fun_prop)
  rw [lintegral_prod _ hA.aemeasurable]
  refine lintegral_congr fun B => ?_
  have hB : Measurable fun p : F × F => K (A, B, p) := hK.comp (by fun_prop)
  rw [lintegral_prod _ hB.aemeasurable]

def dens (g : GL (Fin 2) F) : ℝ≥0∞ := (((modulus (g.val).det ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)

def Hf (f : GL (Fin 2) F → ℝ≥0∞) : (Fin 2 × Fin 2 → F) → ℝ≥0∞ :=
  Function.extend (Measures.glChart F 2).toFun (fun g => dens g * f g) 0

theorem measurable_dens : Measurable (dens (F := F)) := by
  have hc : Continuous fun g : GL (Fin 2) F => (g.val).det := Continuous.matrix_det Units.continuous_val
  exact ((measurable_modulus.comp hc.measurable).pow_const 2).inv.coe_nnreal_ennreal

theorem measurable_Hf {f : GL (Fin 2) F → ℝ≥0∞} (hf : Measurable f) : Measurable (Hf f) :=
  (Measures.glChart F 2).measurableEmbedding.measurable_extend (measurable_dens.mul hf) measurable_const

theorem Hf_zero (f : GL (Fin 2) F → ℝ≥0∞) {x : Fin 2 × Fin 2 → F}
    (hx : x ∉ Set.range (Measures.glChart F 2).toFun) : Hf f x = 0 := by
  rw [Hf, Function.extend_apply' _ _ _ (by simpa using hx)]
  rfl

theorem lint_hG (ψ : AddChar F Circle) (f : GL (Fin 2) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ x, Hf f x ∂(Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ) := by
  have he := (Measures.glChart F 2).measurableEmbedding
  have hd : (fun g : GL (Fin 2) F =>
      (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)) = dens := by
    funext g
    rw [dens, distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]
  rw [LFS.hG, Measures.haarGL_eq, hd, lintegral_withDensity_eq_lintegral_mul _ measurable_dens hf]
  have h1 : ∀ g, ((dens : GL (Fin 2) F → ℝ≥0∞) * f) g = Hf f ((Measures.glChart F 2).toFun g) := fun g =>
    (he.injective.extend_apply _ _ g).symm
  rw [lintegral_congr h1]
  change ∫⁻ g, Hf f ((Measures.glChart F 2).toFun g)
    ∂((Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ).comap (Measures.glChart F 2).toFun) = _
  rw [← he.lintegral_map, he.map_comap, ← lintegral_indicator he.measurableSet_range]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.range (Measures.glChart F 2).toFun
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Hf_zero f hx]

theorem hr_val {r : Fin 2 → F} (h1 : r 1 ≠ 0) : (hr r).val = !![(r 1)⁻¹, 0; r 0, r 1] := by
  have hd : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    simp [Matrix.det_fin_two, h1]
  rw [hr, dif_pos hd]
  rfl

theorem coord_val {y : F} (hy : y ≠ 0) (t : F) {r : Fin 2 → F} (h1 : r 1 ≠ 0) :
    (dg2 (Units.mk0 y hy) 1 * w0 * uni2 t * hr r).val =
      !![y * r 0, y * r 1; -(t * r 0) - 1 / r 1, -(t * r 1)] := by
  simp only [Units.val_mul]
  rw [hr_val h1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, w0, uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem key (f : GL (Fin 2) F → ℝ≥0∞) {y : F} (hy : y ≠ 0) (t : F) {r : Fin 2 → F} (h1 : r 1 ≠ 0) :
    (modulus y : ℝ≥0∞) * Hf f (mat4 (y * r 0, y * r 1, -(t * r 0) - 1 / r 1, -(t * r 1))) =
      f (dg2 (Units.mk0 y hy) 1 * w0 * uni2 t * hr r) * ENNReal.ofReal ((modulus y : ℝ) ^ (-1 : ℤ)) := by
  set g := dg2 (Units.mk0 y hy) 1 * w0 * uni2 t * hr r with hg
  have hv := coord_val hy t h1
  rw [← hg] at hv
  have he : (Measures.glChart F 2).toFun g = mat4 (y * r 0, y * r 1, -(t * r 0) - 1 / r 1, -(t * r 1)) := by
    funext ij
    rcases ij with ⟨i, j⟩
    rw [Measures.glChart_apply, hv]
    rfl
  have hdet : (g.val).det = y := by
    rw [hv, Matrix.det_fin_two_of]
    field_simp
    ring
  have hnn : modulus y ≠ 0 := modulus_ne_zero hy
  have hi : ENNReal.ofReal ((modulus y : ℝ) ^ (-1 : ℤ)) = (((modulus y)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [_root_.zpow_neg_one, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rw [← he, Hf, (Measures.glChart F 2).measurableEmbedding.injective.extend_apply, dens, hdet, hi,
    ← mul_assoc, ← ENNReal.coe_mul, mul_comm]
  congr 2
  field_simp

theorem gjm2 : Ad3.K.GL2LocalData.GJm2 := by
  intro F _ _ _ _ _ _ ψ _ f hf
  have hH := measurable_Hf hf
  have hK : Measurable fun p : F × F × F × F => Hf f (mat4 p) := hH.comp measurable_entries_four
  have h0 : ∀ A B C D : F, A * D - B * C = 0 → Hf f (mat4 (A, B, C, D)) = 0 := by
    intro A B C D h
    refine Hf_zero f ?_
    rintro ⟨g, hg⟩
    have hdet : (g.val).det = 0 := by
      rw [Matrix.det_fin_two]
      have e := fun i j => congrFun hg (i, j)
      simp only [Measures.glChart_apply] at e
      rw [e 0 0, e 0 1, e 1 0, e 1 1]
      simpa [mat4] using h
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero hdet
  rw [lint_hG ψ f hf, pi_eq_map, lintegral_map hH measurable_entries_four, lint4 _ hK, core _ _ hK h0]
  set ν := selfDualMeasure ψ
  set K : F × F × F × F → ℝ≥0∞ := fun p => Hf f (mat4 p)
  have hQ := measurable_Qc hK
  let W : F × F → ℝ≥0∞ := fun p => ∫⁻ t, ∫⁻ y, Qc K p.1 p.2 t y ∂ν ∂ν
  have hW : Measurable W := by
    have h3 : Measurable fun z : (F × F) × F × F => Qc K z.1.1 z.1.2 z.2.1 z.2.2 :=
      hQ.comp (f := fun z : (F × F) × F × F => (z.1.1, z.1.2, z.2.1, z.2.2)) (by fun_prop)
    have h4 : Measurable fun z : ((F × F) × F) × F => Qc K z.1.1.1 z.1.1.2 z.1.2 z.2 :=
      hQ.comp (f := fun z : ((F × F) × F) × F => (z.1.1.1, z.1.1.2, z.1.2, z.2)) (by fun_prop)
    exact (h4.lintegral_prod_right').lintegral_prod_right'
  have hT : ∀ r : Fin 2 → F, W (r 0, r 1) = ∫⁻ t, ∫⁻ y, (if h : y = 0 ∨ r 1 = 0 then 0 else
      f (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * w0 * uni2 t * hr r) *
        ENNReal.ofReal ((modulus y : ℝ) ^ (-1 : ℤ))) ∂ν ∂ν := by
    intro r
    refine lintegral_congr fun t => lintegral_congr fun y => ?_
    by_cases h : y = 0 ∨ r 1 = 0
    · rw [dif_pos h, Qc, if_pos h.symm]
    · rw [dif_neg h, Qc, if_neg (fun h' => h h'.symm)]
      push_neg at h
      exact key f h.1 t h.2
  have hmp := (measurePreserving_piFinTwo fun _ : Fin 2 => ν).lintegral_comp hW
  have hR : ∫⁻ u, ∫⁻ v, W (u, v) ∂ν ∂ν = ∫⁻ r, W (r 0, r 1) ∂LFS.vol2 ψ := by
    rw [← lintegral_prod _ hW.aemeasurable]
    exact hmp.symm
  refine hR.trans (lintegral_congr hT)

end GlobalTheory.CompanionTheory.GL2Coordinates
