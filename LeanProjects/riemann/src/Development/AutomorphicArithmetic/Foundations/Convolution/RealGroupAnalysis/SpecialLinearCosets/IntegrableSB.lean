import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GenSL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical NNReal

namespace UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

private def cjE (x : GL (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃ₜ* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun m := ⟨(x⁻¹).val * m.1 * x.val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]⟩
  invFun m := ⟨x.val * m.1 * (x⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, m.2, mul_one, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]⟩
  left_inv m := by
    apply Subtype.ext
    show x.val * ((x⁻¹).val * m.1 * x.val) * (x⁻¹).val = m.1
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  right_inv m := by
    apply Subtype.ext
    show (x⁻¹).val * (x.val * m.1 * (x⁻¹).val) * x.val = m.1
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  map_mul' m n := by
    apply Subtype.ext
    show (x⁻¹).val * (m.1 * n.1) * x.val = ((x⁻¹).val * m.1 * x.val) * ((x⁻¹).val * n.1 * x.val)
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

private theorem cjE_val (x : GL (Fin 2) K) (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    (cjE x m).1 = (x⁻¹).val * m.1 * x.val := rfl

variable [LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) K)]
  [BorelSpace (Matrix.SpecialLinearGroup (Fin 2) K)]

private noncomputable def cc (x : GL (Fin 2) K) : ℝ≥0 := mulEquivHaarChar (cjE x)

private theorem cc_ne (x : GL (Fin 2) K) : cc x ≠ 0 := (mulEquivHaarChar_pos (cjE x)).ne'

private theorem cc_mul (x y : GL (Fin 2) K) : cc (x * y) = cc x * cc y := by
  have h : cjE (x * y) = (cjE x).trans (cjE y) := by
    ext1 m
    apply Subtype.ext
    show ((x * y)⁻¹).val * m.1 * (x * y).val = (y⁻¹).val * ((x⁻¹).val * m.1 * x.val) * y.val
    simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]
  unfold cc
  rw [h, mulEquivHaarChar_trans]

private theorem cc_central (z : GL (Fin 2) K) (hz : ∀ m : Matrix (Fin 2) (Fin 2) K, z.val * m = m * z.val) :
    cc z = 1 := by
  have h : cjE z = ContinuousMulEquiv.refl _ := by
    ext1 m
    apply Subtype.ext
    show (z⁻¹).val * m.1 * z.val = m.1
    rw [mul_assoc, ← hz, Units.inv_mul_cancel_left]
  unfold cc
  rw [h, mulEquivHaarChar_refl]

private theorem cc_of_sq (d t : GL (Fin 2) K) (h : d * t = t * t * d) : cc t = 1 := by
  have e := congrArg cc h
  rw [cc_mul, cc_mul, cc_mul] at e
  apply mul_left_cancel₀ (mul_ne_zero (cc_ne t) (cc_ne d))
  rw [mul_one, show cc t * cc d * cc t = cc t * cc t * cc d by ring, ← e]
  ring

variable (K) in

private noncomputable def ccS : Matrix.SpecialLinearGroup (Fin 2) K →* ℝ≥0 where
  toFun g := cc (Matrix.SpecialLinearGroup.toGL g)
  map_one' := by
    rw [map_one]
    exact cc_central 1 (by simp)
  map_mul' g h := by rw [map_mul, cc_mul]

private theorem cc_SL (h2 : (2 : K) ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    cc (Matrix.SpecialLinearGroup.toGL g) = 1 := by
  let d₁ : GL (Fin 2) K := ⟨!![2, 0; 0, 1], !![2⁻¹, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  let d₂ : GL (Fin 2) K := ⟨!![1, 0; 0, 2], !![1, 0; 0, 2⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [h2]⟩
  have hT := UpperTheory.ConvolutionTheory.R2.I.genSL K (ccS K).ker
    (fun g b hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₁ _ (Units.ext ?_)
      show d₁.val * g.1 = g.1 * g.1 * d₁.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
    (fun g c hg => by
      rw [MonoidHom.mem_ker]
      refine cc_of_sq d₂ _ (Units.ext ?_)
      show d₂.val * g.1 = g.1 * g.1 * d₂.val
      rw [hg]
      ext i j; fin_cases i <;> fin_cases j <;> simp [d₂, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
  have : g ∈ (ccS K).ker := by rw [hT]; trivial
  exact this

private theorem cc_eq_one (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) : cc x = 1 := by
  have hd : x.val.det ≠ 0 := by
    intro h0
    have h1 : x.val.det * (x⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  set t := x.val.det with ht
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨t⁻¹ • (x.val * x.val), by
    rw [Matrix.det_smul, Matrix.det_mul, ← ht]
    simp only [Fintype.card_fin]
    field_simp⟩
  let z : GL (Fin 2) K := ⟨t • 1, t⁻¹ • 1, by simp [smul_smul, hd], by simp [smul_smul, hd]⟩
  have hx : x * x = z * Matrix.SpecialLinearGroup.toGL s := by
    apply Units.ext
    show x.val * x.val = (t • (1 : Matrix (Fin 2) (Fin 2) K)) * (t⁻¹ • (x.val * x.val))
    simp [smul_smul, hd]
  have hz : cc z = 1 := cc_central z (fun m => by
    show (t • (1 : Matrix (Fin 2) (Fin 2) K)) * m = m * (t • (1 : Matrix (Fin 2) (Fin 2) K))
    simp)
  have e := congrArg cc hx
  rw [cc_mul, cc_mul, hz, cc_SL h2, one_mul] at e
  have e' : ((cc x : ℝ≥0) : ℝ) * (cc x : ℝ≥0) = 1 := by exact_mod_cast e
  rcases mul_self_eq_one_iff.1 e' with h | h
  · exact_mod_cast h
  · have := (cc x).coe_nonneg
    linarith

private theorem mp_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K) :
    MeasurePreserving (cjE x) (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) Measure.haar := by
  refine ⟨(map_continuous (cjE x)).measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (cjE x)
  have h1 : mulEquivHaarChar (cjE x) = 1 := cc_eq_one h2 x
  rwa [h1, one_smul] at h

private theorem integral_cjE (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K)
    (f : Matrix.SpecialLinearGroup (Fin 2) K → ℂ) :
    ∫ m, f (cjE x m) ∂(Measure.haar) = ∫ m, f m ∂(Measure.haar) :=
  (mp_cjE h2 x).integral_comp (cjE x).toHomeomorph.measurableEmbedding f

private theorem integrable_SB (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Integrable a.1 (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) :=
  a.2.1.continuous.integrable_of_hasCompactSupport a.2.2

private theorem exists_I (h2 : (2 : K) ≠ 0) :
    ∃ I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ,
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a) ∧
      (∀ (x : GL (Fin 2) K) (a a' : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        (∀ m m' : Matrix.SpecialLinearGroup (Fin 2) K, m'.1 = (x⁻¹).val * m.1 * x.val → a'.1 m = a.1 m') →
          I a' = I a) ∧
      (∀ (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (a : SB (Matrix.SpecialLinearGroup (Fin 2) K)),
        IsOpen (U : Set (Matrix.SpecialLinearGroup (Fin 2) K)) → a.1 = ind U → I a ≠ 0) := by
  let I : SB (Matrix.SpecialLinearGroup (Fin 2) K) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ m, a.1 m ∂(Measure.haar)
      map_add' := fun a b => integral_add (integrable_SB a) (integrable_SB b)
      map_smul' := fun c a => integral_smul c a.1 }
  have hI : ∀ a, I a = ∫ m, a.1 m ∂(Measure.haar) := fun _ => rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · intro g a a' h
    have hm : ∀ m, m * g = g * cjE (Matrix.SpecialLinearGroup.toGL g) m := by
      intro m
      apply Subtype.ext
      show m.1 * g.1 = g.1 * (((Matrix.SpecialLinearGroup.toGL g)⁻¹).val * m.1 * (Matrix.SpecialLinearGroup.toGL g).val)
      have e : g.1 * ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val = 1 :=
        Units.mul_inv (Matrix.SpecialLinearGroup.toGL g)
      rw [← mul_assoc, ← mul_assoc, e, one_mul]
      rfl
    rw [hI, hI]
    simp_rw [h, hm]
    rw [integral_cjE h2 _ (fun y => a.1 (g * y))]
    exact integral_mul_left_eq_self a.1 g
  · intro x a a' h
    rw [hI, hI]
    simp_rw [fun m => h m (cjE x m) rfl]
    exact integral_cjE h2 x a.1
  · intro U a hU ha
    have hs : Function.support a.1 = (U : Set _) := by
      rw [ha]
      ext m
      by_cases hm : m ∈ (U : Set _) <;> simp [ind, hm]
    have hfin : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ ⊤ := by
      have hc : IsCompact (tsupport a.1) := a.2.2
      exact ((measure_mono (hs ▸ subset_tsupport a.1)).trans_lt hc.measure_lt_top).ne
    have hpos : (Measure.haar : Measure (Matrix.SpecialLinearGroup (Fin 2) K)) (U : Set _) ≠ 0 :=
      (hU.measure_pos _ ⟨1, U.one_mem⟩).ne'
    rw [hI, ha]
    unfold ind
    rw [integral_indicator_const _ hU.measurableSet]
    simp only [Measure.real, smul_eq_mul, Complex.real_smul, mul_one]
    exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩)

end

end UpperTheory.ConvolutionTheory.R2.I.CentralConjugation

theorem UpperTheory.ConvolutionTheory.R2.I.invI :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∃ I : SB (SL v) →ₗ[ℂ] ℂ, InvI I := by
  intro F _ _ v
  letI : MeasurableSpace (SL v) := borel _
  haveI : BorelSpace (SL v) := ⟨rfl⟩
  haveI : LocallyCompactSpace (M2 v) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Kv v))
  haveI : LocallyCompactSpace (SL v) :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := Kv v)).locallyCompactSpace
  have h2 : (2 : Kv v) ≠ 0 := by
    haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
    exact two_ne_zero
  obtain ⟨I, h₁, h₂, h₃⟩ := UpperTheory.ConvolutionTheory.R2.I.CentralConjugation.exists_I (K := Kv v) h2
  exact ⟨I, ⟨h₁, h₂, h₃⟩⟩
