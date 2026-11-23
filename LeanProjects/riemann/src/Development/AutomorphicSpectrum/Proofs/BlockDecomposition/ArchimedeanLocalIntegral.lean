import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import GroundTheory.AutomorphicForms.GL2Classical.KFinite
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RealArchimedeanCharacter

open Ad3 Ad3.R
open RationalIdeles (realEquiv realUnitsEquiv)

theorem integral_inf (G : ℝˣ → ℂ) :
    ∫ a : (InfiniteAdeleRing ℚ)ˣ, G (realUnitsEquiv a) ∂infiniteIdeleMeasure ℚ =
      ∫ x : ℝ, (if h : x = 0 then 0 else G (Units.mk0 x h)) / ((|x| : ℝ) : ℂ) := by
  have he : MeasurableEmbedding (infiniteUnitsEquiv ℚ).symm :=
    (infiniteUnitsEquiv ℚ).symm.toHomeomorph.measurableEmbedding
  rw [infiniteIdeleMeasure, he.integral_map]
  have hinj : ∀ w : InfinitePlace ℚ, Function.Injective (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (RationalIdeles.isReal_infinitePlace w)) := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (RationalIdeles.isReal_infinitePlace w)).injective
  let g : ∀ w : InfinitePlace ℚ, w.Completion → ℂ := fun w u =>
    (fun x : ℝ => if h : x = 0 then 0 else G (Units.mk0 x h))
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal (RationalIdeles.isReal_infinitePlace w) u)
  have hfub := integral_fintype_prod_eq_prod
    (μ := fun w : InfinitePlace ℚ ↦ infinitePlaceUnitsMeasure w) (fun w (u : (w.Completion)ˣ) => g w u)
  have hpt : ∀ y : Π w : InfinitePlace ℚ, (w.Completion)ˣ,
      G (realUnitsEquiv ((infiniteUnitsEquiv ℚ).symm y)) = ∏ w, g w (y w) := by
    intro y
    rw [Fintype.prod_unique]
    have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (RationalIdeles.isReal_infinitePlace default) ((y default : (InfinitePlace.Completion (default : InfinitePlace ℚ))ˣ) : _) ≠ 0 := by
      intro h
      exact (y default).ne_zero ((map_eq_zero_iff _ (hinj default)).1 h)
    simp only [g, dif_neg h0]
    congr 1
    exact Units.ext rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hfub, Fintype.prod_unique,
    integral_infinitePlaceUnitsMeasure_of_isReal (RationalIdeles.isReal_infinitePlace default)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : InfinitePlace.Completion.extensionEmbeddingOfIsReal (RationalIdeles.isReal_infinitePlace default)
      ((InfinitePlace.Completion.isometryEquivRealOfIsReal (RationalIdeles.isReal_infinitePlace default)).symm x) = x :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (RationalIdeles.isReal_infinitePlace default)).apply_symm_apply x
  simp only [g, hx]

theorem infMod_eq (a : (InfiniteAdeleRing ℚ)ˣ) :
    GodementSection.infMod a = |((realUnitsEquiv a : ℝˣ) : ℝ)| := by
  have hw := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  rw [GodementSection.infMod, Fintype.prod_unique, InfinitePlace.mult, if_pos hw, pow_one]
  rw [← Real.norm_eq_abs]
  exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm

theorem infChar_pos (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c) (a : (InfiniteAdeleRing ℚ)ˣ)
    (ha : 0 < ((realUnitsEquiv a : ℝˣ) : ℝ)) : GodementSection.infChar c a = 1 := by
  obtain ⟨n, hn, hpow⟩ := c.exists_toIdele_pow_eq_one hc
  set t : ℝ := ((realUnitsEquiv a : ℝˣ) : ℝ) with ht
  have hu : (t ^ (1 / (n : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  set b : (InfiniteAdeleRing ℚ)ˣ := realUnitsEquiv.symm (Units.mk0 _ hu) with hb
  have hab : a = b ^ n := by
    apply realUnitsEquiv.injective
    rw [map_pow, hb, ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [hab, map_pow]
  exact hpow _

theorem infChar_neg_one (c : HeckeCharacter ℚ) (δ : Bool)
    (hδ : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) :
    (GodementSection.infChar c (-1) : ℂ) = if δ then -1 else 1 := by
  rw [GodementSection.infChar, MonoidHom.comp_apply, HeckeCharacter.toIdele_ofInfinite, Fintype.prod_unique, ← hδ default]
  congr 3

theorem infChar_neg (c : HeckeCharacter ℚ) (δ : Bool) (hc : IsOfFinOrder c)
    (hδ : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (a : (InfiniteAdeleRing ℚ)ˣ) (ha : ((realUnitsEquiv a : ℝˣ) : ℝ) < 0) :
    (GodementSection.infChar c a : ℂ) = if δ then -1 else 1 := by
  have h1 : GodementSection.infChar c (-a) = 1 := by
    apply infChar_pos c hc
    have : realUnitsEquiv (-a) = - realUnitsEquiv a := by
      apply Units.ext
      change realEquiv (-(a : InfiniteAdeleRing ℚ)) = -(realEquiv a)
      rw [map_neg]
    rw [this]
    simpa using ha
  have h2 : a = (-1) * (-a) := by simp
  rw [h2, map_mul, h1, mul_one]
  exact infChar_neg_one c δ hδ

theorem infChar_sq (c : HeckeCharacter ℚ) (δ : Bool) (hc : IsOfFinOrder c)
    (hδ : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (a : (InfiniteAdeleRing ℚ)ˣ) : (GodementSection.infChar (c * c⁻¹⁻¹) a : ℂ) = 1 := by
  have hm : GodementSection.infChar (c * c⁻¹⁻¹) a = GodementSection.infChar c a * GodementSection.infChar c a := by
    rw [inv_inv]; rfl
  rw [hm, Circle.coe_mul]
  rcases lt_or_gt_of_ne (realUnitsEquiv a).ne_zero with h | h
  · rw [infChar_neg c δ hc hδ a h]
    cases δ <;> simp
  · rw [infChar_pos c hc a h]
    simp

theorem realPart_mul (x y : AdelicGLn.AdelicGL ℚ 2) : realPart (x * y) = realPart x * realPart y := by
  have h : (AdelicGLn.prodEquiv ℚ 2 (x * y)).1 = (AdelicGLn.prodEquiv ℚ 2 x).1 * (AdelicGLn.prodEquiv ℚ 2 y).1 := by
    rw [map_mul]; rfl
  change GeneralLinearGroup.map realEquiv.toRingHom _ = GeneralLinearGroup.map realEquiv.toRingHom _ *
    GeneralLinearGroup.map realEquiv.toRingHom _
  rw [h, map_mul]

theorem realPart_diag (a : (InfiniteAdeleRing ℚ)ˣ) :
    realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1) = dg2 (realUnitsEquiv a) 1 := by
  have h1 : ((((IdeleGroup.prodEquiv ℚ).symm (a, 1) : IdeleGroup ℚ) : 𝔸[ℚ]).1) = (a : InfiniteAdeleRing ℚ) :=
    GodementSection.val_symm_fst (a, 1)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change realEquiv ((dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 : GL (Fin 2) 𝔸[ℚ]) i j).1 = _
  fin_cases i <;> fin_cases j
  · exact congrArg realEquiv h1
  · simp [dg2]
  · simp [dg2]
  · simp [dg2]; rfl

theorem det_real (g : AdelicGLn.AdelicGL ℚ 2) :
    realUnitsEquiv (GeneralLinearGroup.det (AdelicGLn.prodEquiv ℚ 2 g).1) = GeneralLinearGroup.det (realPart g) := by
  apply Units.ext
  change realEquiv ((AdelicGLn.prodEquiv ℚ 2 g).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)).det =
    ((realPart g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  rfl

theorem gauss_eval (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (hγ : IsGauss γ) (κ : KA)
    (a : (InfiniteAdeleRing ℚ)ˣ) :
    γ (GodementSection.infVec (![0, (a : InfiniteAdeleRing ℚ)] ᵥ*
      ((AdelicGLn.prodEquiv ℚ 2 κ.1).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)))) =
      realGaussian ((realUnitsEquiv a : ℝˣ) : ℝ) := by
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) := ((AdelicGLn.prodEquiv ℚ 2 κ.1).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) with hM
  set R : GL (Fin 2) ℝ := realPart κ.1 with hR
  set t : ℝ := ((realUnitsEquiv a : ℝˣ) : ℝ) with ht
  have hy : ∀ (i : Fin 2) (w : {w : InfinitePlace ℚ // w.IsReal}),
      (GodementSection.infVec (![0, (a : InfiniteAdeleRing ℚ)] ᵥ* M) i).1 w = t * R 1 i := by
    intro i w
    obtain ⟨w, hw⟩ := w
    obtain rfl : w = default := Subsingleton.elim _ _
    have h2 : (![0, (a : InfiniteAdeleRing ℚ)] ᵥ* M) i = a * M 1 i := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h3 : (GodementSection.infVec (![0, (a : InfiniteAdeleRing ℚ)] ᵥ* M) i).1 ⟨default, hw⟩ =
        realEquiv ((![0, (a : InfiniteAdeleRing ℚ)] ᵥ* M) i) := by
      rfl
    rw [h3, h2, map_mul]
    rfl
  have hU : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    ⟨⟨⟨default, RationalIdeles.isReal_infinitePlace _⟩⟩, fun w => Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨h00, h11, h01⟩ := GroundTheory.Automorphic.GL2Classical.realPart_orthogonal κ.2
  rw [hγ, realGaussian_eq_ofReal]
  simp only [hy, Fintype.sum_unique, Fin.sum_univ_two]
  congr 2
  linear_combination (-Real.pi * t ^ 2) * h11

theorem WW_eq (k : ℕ) (t : ℝˣ) : WR k t * conj (WR k t) =
    if (t : ℝ) < 0 then ((|(t : ℝ)| ^ k * Real.exp (-(4 * Real.pi * |(t : ℝ)|)) : ℝ) : ℂ) else 0 := by
  unfold WR
  split_ifs with h
  · rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    have h1 : (Real.sqrt |(t : ℝ)| ^ k) * (Real.sqrt |(t : ℝ)| ^ k) = |(t : ℝ)| ^ k := by
      rw [← mul_pow, Real.mul_self_sqrt (abs_nonneg _)]
    have h2 : Real.exp (-2 * Real.pi * |(t : ℝ)|) * Real.exp (-2 * Real.pi * |(t : ℝ)|) =
        Real.exp (-(4 * Real.pi * |(t : ℝ)|)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ = (Real.sqrt |(t : ℝ)| ^ k * Real.sqrt |(t : ℝ)| ^ k) *
          (Real.exp (-2 * Real.pi * |(t : ℝ)|) * Real.exp (-2 * Real.pi * |(t : ℝ)|)) := by ring
      _ = _ := by rw [h1, h2]
  · simp

def pp (k : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  ((y ^ k * Real.exp (-(4 * Real.pi * y)) : ℝ) : ℂ) * (y : ℂ) ^ (s - 1) / (y : ℂ)

theorem integral_pp (k : ℕ) (s : ℂ) (hs : 0 < (s + k - 1).re) :
    ∫ y in Set.Ioi (0 : ℝ), pp k s y = (1 / (4 * Real.pi : ℂ)) ^ (s + k - 1) * Complex.Gamma (s + k - 1) := by
  have hr : 0 < 4 * Real.pi := by positivity
  have h0 := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
  push_cast at h0
  rw [← h0]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
  simp only [pp]
  have e1 : (y : ℂ) ^ (s + k - 1 - 1) = (y : ℂ) ^ k * (y : ℂ) ^ (s - 1) / (y : ℂ) := by
    rw [show s + k - 1 - 1 = (k : ℂ) + (s - 1) - 1 by ring, Complex.cpow_sub _ _ hy0, Complex.cpow_add _ _ hy0,
      Complex.cpow_natCast, Complex.cpow_one]
  rw [e1]
  push_cast
  ring

theorem integral_pos (k : ℕ) (s : ℂ) :
    ∫ x : ℝ, (if 0 < x then pp k s x else 0) = ∫ y in Set.Ioi (0 : ℝ), pp k s y := by
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Set.indicator]

theorem integral_neg (k : ℕ) (s : ℂ) (e : ℂ) :
    ∫ x : ℝ, (if x < 0 then e * pp k s (-x) else 0) = e * ∫ y in Set.Ioi (0 : ℝ), pp k s y := by
  rw [← integral_pos, ← integral_const_mul, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases h : 0 < x
  · simp [h]
  · have : ¬ (-x < 0) := by simpa using h
    simp [h]

theorem det_sq (κ : KA) :
    ((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) = 1 ∨ ((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) = -1 := by
  obtain ⟨h00, h11, h01⟩ := GroundTheory.Automorphic.GL2Classical.realPart_orthogonal κ.2
  have hd : ((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) =
      realPart κ.1 0 0 * realPart κ.1 1 1 - realPart κ.1 0 1 * realPart κ.1 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have h2 : ((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) ^ 2 = 1 := by
    rw [hd]
    have : (realPart κ.1 0 0 * realPart κ.1 1 1 - realPart κ.1 0 1 * realPart κ.1 1 0) ^ 2 =
        (realPart κ.1 0 0 ^ 2 + realPart κ.1 0 1 ^ 2) * (realPart κ.1 1 0 ^ 2 + realPart κ.1 1 1 ^ 2) -
          (realPart κ.1 0 0 * realPart κ.1 1 0 + realPart κ.1 0 1 * realPart κ.1 1 1) ^ 2 := by ring
    rw [this, h00, h11, h01]; norm_num
  have h3 : (((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) - 1) * (((GeneralLinearGroup.det (realPart κ.1) : ℝˣ) : ℝ) + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · left; linarith
  · right; linarith

theorem orth (κ : KA) : (realPart κ.1).val * (realPart κ.1).valᵀ = 1 := by
  obtain ⟨h00, h11, h01⟩ := GroundTheory.Automorphic.GL2Classical.realPart_orthogonal κ.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem arch_eval (c : HeckeCharacter ℚ) (δ : Bool) (hc : IsOfFinOrder c)
    (hδ : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (γ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (hγ : IsGauss γ) (s : ℂ) (hs : 0 < s.re) (κ : KA) :
    archSection c c⁻¹ s γ (AdelicGLn.prodEquiv ℚ 2 κ.1).1 =
      (GodementSection.infChar c (GeneralLinearGroup.det (AdelicGLn.prodEquiv ℚ 2 κ.1).1) : ℂ) *
        Complex.Gammaℝ (2 * s) := by
  have h1 : GodementSection.infMod (GeneralLinearGroup.det (AdelicGLn.prodEquiv ℚ 2 κ.1).1) = 1 := by
    rw [infMod_eq, det_real]
    rcases det_sq κ with h | h <;> simp [h]
  rw [archSection, h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
  congr 1
  obtain ⟨G, hG⟩ : ∃ G : ℝˣ → ℂ, G = fun t : ℝˣ => realGaussian (t : ℝ) * ((|(t : ℝ)| : ℝ) : ℂ) ^ (2 * s) := ⟨_, rfl⟩
  have h2 : ∀ a : (InfiniteAdeleRing ℚ)ˣ, γ (GodementSection.infVec (![0, (a : InfiniteAdeleRing ℚ)] ᵥ*
        ((AdelicGLn.prodEquiv ℚ 2 κ.1).1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)))) *
        (GodementSection.infChar (c * c⁻¹⁻¹) a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (2 * s) =
      G (realUnitsEquiv a) := by
    intro a
    rw [gauss_eval γ hγ κ a, infChar_sq c δ hc hδ a, infMod_eq, mul_one, hG]
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_inf G,
    ← integral_realGaussian_mul_abs_cpow (s := 2 * s) (by simpa using hs)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, hG]

theorem real_torus_sign_flip (t : ℝˣ) (R : GL (Fin 2) ℝ) : dg2 t 1 * R = dg2 (-t) 1 * (dg2 (-1) 1 * R) := by
  rw [← mul_assoc]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

def sg (e : ℂ) (x : ℝ) : ℂ := if x < 0 then e else 1

theorem sg_neg (e : ℂ) {x : ℝ} (h : x < 0) : sg e x = e := if_pos h

theorem sg_pos (e : ℂ) {x : ℝ} (h : 0 < x) : sg e x = 1 := if_neg (not_lt.2 h.le)

theorem torus_one (k : ℕ) (c : HeckeCharacter ℚ) (δ : Bool) (hc : IsOfFinOrder c)
    (hδ : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1)
    (s : ℂ) (κ : KA) (Q : GL (Fin 2) ℝ → ℂ)
    (hQ : ∀ t : ℝˣ, Q (dg2 t 1 * realPart κ.1) = WR k t * conj (WR k t)) :
    ∫ a : (InfiniteAdeleRing ℚ)ˣ, Q (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ =
      (if δ then -1 else 1) * ∫ y in Set.Ioi (0 : ℝ), pp k s y := by
  set e : ℂ := if δ then -1 else 1 with he
  obtain ⟨G, hG⟩ : ∃ G : ℝˣ → ℂ, G = fun t : ℝˣ => (WR k t * conj (WR k t)) * sg e (t : ℝ) * ((|(t : ℝ)| : ℝ) : ℂ) ^ (s - 1) := ⟨_, rfl⟩
  have h2 : ∀ a : (InfiniteAdeleRing ℚ)ˣ, Q (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) =
      G (realUnitsEquiv a) := by
    intro a
    rw [realPart_mul, realPart_diag, hQ, infMod_eq, hG]
    congr 2
    rcases lt_or_gt_of_ne (realUnitsEquiv a).ne_zero with h | h
    · rw [sg_neg e h, infChar_neg c δ hc hδ a h]
    · rw [sg_pos e h, infChar_pos c hc a h]; simp
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_inf G, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x = 0
  · simp [hx]
  simp only [dif_neg hx, hG, WW_eq, Units.val_mk0]
  by_cases hn : x < 0
  · simp only [if_pos hn, abs_of_neg hn, pp, sg_neg e hn]
    ring
  · simp [hn]

theorem torus_neg (k : ℕ) (c : HeckeCharacter ℚ) (hc : IsOfFinOrder c)
    (s : ℂ) (κ : KA) (Q : GL (Fin 2) ℝ → ℂ)
    (hQ : ∀ t : ℝˣ, Q (dg2 t 1 * realPart κ.1) = WR k (-t) * conj (WR k (-t))) :
    ∫ a : (InfiniteAdeleRing ℚ)ˣ, Q (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ =
      ∫ y in Set.Ioi (0 : ℝ), pp k s y := by
  obtain ⟨G, hG⟩ : ∃ G : ℝˣ → ℂ, G = fun t : ℝˣ => (WR k (-t) * conj (WR k (-t))) * ((|(t : ℝ)| : ℝ) : ℂ) ^ (s - 1) := ⟨_, rfl⟩
  have h2 : ∀ a : (InfiniteAdeleRing ℚ)ˣ, Q (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) =
      G (realUnitsEquiv a) := by
    intro a
    rw [realPart_mul, realPart_diag, hQ, infMod_eq, hG]
    rcases lt_or_gt_of_ne (realUnitsEquiv a).ne_zero with h | h
    · have : WR k (-(realUnitsEquiv a)) = 0 := by
        simp [WR, h.le]
      simp [this]
    · rw [infChar_pos c hc a h]; simp
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_inf G, ← integral_pos]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x = 0
  · simp [hx]
  simp only [dif_neg hx, hG, WW_eq, Units.val_mk0, Units.val_neg]
  by_cases hn : 0 < x
  · have h' : -x < 0 := by simpa using hn
    simp only [if_pos h', if_pos hn, abs_neg, abs_of_pos hn, pp]
  · have h' : ¬ (-x < 0) := by simpa using hn
    simp [hn, h']

def CC (k : ℕ) : ℂ := (1 / 4 : ℂ) * Complex.exp (-(Real.log 2 : ℂ) * ((k : ℂ) - 1))

theorem CC_ne (k : ℕ) : CC k ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

theorem ofReal_cpow_exp {x : ℝ} (hx : 0 < x) (z : ℂ) : (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem gamma_const (k : ℕ) (s : ℂ) :
    Complex.Gammaℝ (2 * s) * ((1 / (4 * Real.pi : ℂ)) ^ (s + k - 1) * Complex.Gamma (s + k - 1)) = CC k * GG k s := by
  have hpi := Real.pi_pos
  have hl1 : Real.log (1 / (4 * Real.pi)) = -(2 * Real.log 2 + Real.log Real.pi) := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hpi.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hpi.ne'
  have e1 : (1 / (4 * Real.pi : ℂ)) ^ (s + k - 1) = Complex.exp (-(2 * (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ)) * (s + k - 1)) := by
    have : (1 / (4 * Real.pi : ℂ)) = ((1 / (4 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ofReal_cpow_exp (by positivity), hl1]
    push_cast; rfl
  have e2 : ∀ z : ℂ, (2 * Real.pi : ℂ) ^ (-z) = Complex.exp (-((Real.log 2 : ℂ) + (Real.log Real.pi : ℂ)) * z) := by
    intro z
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ofReal_cpow_exp (by positivity), hl2]
    push_cast; congr 1; ring
  have e3 : (Real.pi : ℂ) ^ (-(2 * s) / 2) = Complex.exp (-(Real.log Real.pi : ℂ) * s) := by
    rw [ofReal_cpow_exp hpi]
    congr 1; ring
  rw [Complex.Gammaℝ_def, GG, Complex.Gammaℂ_def, Complex.Gammaℂ_def, e1, e2, e2, e3, CC,
    show 2 * s / 2 = s by ring]
  have key : Complex.exp (-(Real.log Real.pi : ℂ) * s) * Complex.exp (-(2 * (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ)) * (s + k - 1)) =
      Complex.exp (-(Real.log 2 : ℂ) * ((k : ℂ) - 1)) * (Complex.exp (-((Real.log 2 : ℂ) + (Real.log Real.pi : ℂ)) * s) *
        Complex.exp (-((Real.log 2 : ℂ) + (Real.log Real.pi : ℂ)) * (s + k - 1))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  linear_combination (Complex.Gamma s * Complex.Gamma (s + k - 1)) * key

theorem E5 : Ad3.R.E5 := by
  intro k hk
  refine ⟨CC k, CC_ne k, ?_⟩
  intro γ hγ c δ hc hδ s hs κ Q hQ
  have hs0 : 0 < s.re := by linarith
  have hw : 0 < (s + k - 1).re := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith
  rw [arch_eval c δ hc hδ γ hγ s hs0 κ]
  have hdet : realUnitsEquiv (GeneralLinearGroup.det (AdelicGLn.prodEquiv ℚ 2 κ.1).1) =
      GeneralLinearGroup.det (realPart κ.1) := det_real κ.1
  rcases det_sq κ with h | h
  · have hd : (GeneralLinearGroup.det (realPart κ.1)).val = 1 := h
    rw [torus_one k c δ hc hδ s κ Q (fun t => hQ t _ (orth κ) hd), integral_pp k s hw,
      infChar_pos c hc _ (by rw [hdet, h]; norm_num)]
    have := gamma_const k s
    simp only [Circle.coe_one, one_mul]
    linear_combination (if δ then (-1 : ℂ) else 1) * this
  · have hR : ∀ t : ℝˣ, Q (dg2 t 1 * realPart κ.1) = WR k (-t) * conj (WR k (-t)) := by
      intro t
      rw [real_torus_sign_flip]
      refine hQ (-t) _ ?_ ?_
      · have h0 := orth κ
        have hD : (dg2 (-1 : ℝˣ) (1 : ℝˣ)).val * (dg2 (-1 : ℝˣ) (1 : ℝˣ)).valᵀ = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
        rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (dg2 (-1 : ℝˣ) (1 : ℝˣ)).valᵀ, h0,
          Matrix.one_mul, hD]
      · rw [map_mul, Units.val_mul, h]
        have : ((GeneralLinearGroup.det (dg2 (-1 : ℝˣ) (1 : ℝˣ)) : ℝˣ) : ℝ) = -1 := by
          rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
          simp [dg2]
        rw [this]; norm_num
    rw [torus_neg k c hc s κ Q hR, integral_pp k s hw,
      infChar_neg c δ hc hδ _ (by rw [hdet, h]; norm_num)]
    have := gamma_const k s
    linear_combination (if δ then (-1 : ℂ) else 1) * this

end GlobalTheory.CompanionTheory.RealArchimedeanCharacter

end
