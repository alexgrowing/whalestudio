import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.RSUnfold

section Alg
variable {R : Type*} [CommRing R]

theorem unipotent_mul_unipotent_add (x y : R) : uni2 x * uni2 y = uni2 (x + y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem diagonal_mul_diagonal_alt (a b c d : Rˣ) : dg2 a b * dg2 c d = dg2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_mul_unipotent (a : Rˣ) (x : R) : dg2 a 1 * uni2 x = uni2 ((a : R) * x) * dg2 a 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem vecMul_unipotent_bottom_row (c x : R) : ![0, c] ᵥ* ((uni2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![0, c] := by
  ext i
  fin_cases i <;> simp [uni2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_diagonal_bottom_row (c : R) (a b : Rˣ) :
    ![0, c] ᵥ* ((dg2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![0, c * b] := by
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end Alg

def e0 : Fin 2 → ℚ := ![0, 1]

def pp (α : ℚˣ) (b : ℚ) : GL (Fin 2) ℚ := dg2 α 1 * uni2 b

theorem rationalEmbedding_unipotent (b : ℚ) : dia2 (uni2 b) = uni2 (algebraMap ℚ 𝔸[ℚ] b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, AdelicGLn.diagonal]

theorem rationalEmbedding_diagonal (α : ℚˣ) : dia2 (dg2 α 1) = dg2 (pri α) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, pri, AdelicGLn.diagonal]

theorem mirabolic_mul_iwasawa_coordinates (α : ℚˣ) (b : ℚ) (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    dia2 (pp α b) * pt x a z κ =
      pt ((pri α : 𝔸[ℚ]) * (x + algebraMap ℚ 𝔸[ℚ] b)) (pri α * a) z κ := by
  have h : (dg2 (pri α) 1 : G2) * uni2 (algebraMap ℚ 𝔸[ℚ] b + x) * dg2 a 1 =
      uni2 ((pri α : 𝔸[ℚ]) * (x + algebraMap ℚ 𝔸[ℚ] b)) * dg2 (pri α * a) 1 := by
    rw [diagonal_mul_unipotent, mul_assoc, diagonal_mul_diagonal_alt, mul_one, add_comm]
  simp only [pp, pt, map_mul, rationalEmbedding_unipotent, rationalEmbedding_diagonal]
  rw [← h, ← unipotent_mul_unipotent_add]
  simp only [mul_assoc]

theorem row_dia (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (g : G2) :
    row ξ (dia2 γ * g) = row (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) g := by
  unfold Ad3.R.row
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, AdelicGLn.diagonal]

theorem bottom_row_iwasawa_coordinates (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) : row e0 (pt x a z κ) = lrow z κ := by
  have h0 : (fun i => algebraMap ℚ 𝔸[ℚ] (e0 i)) = ![0, 1] := by
    ext i
    fin_cases i <;> simp [e0]
  unfold Ad3.R.row lrow pt
  rw [h0]
  simp only [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_unipotent_bottom_row, vecMul_diagonal_bottom_row, one_mul, Units.val_one, mul_one]

theorem bottom_row_vector_mirabolic_fixed (α : ℚˣ) (b : ℚ) : e0 ᵥ* ((pp α b : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = e0 := by
  unfold pp e0
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_diagonal_bottom_row, vecMul_unipotent_bottom_row]
  simp

theorem bottom_row_mirabolic_invariance (α : ℚˣ) (b : ℚ) (g : G2) : row e0 (dia2 (pp α b) * g) = row e0 g := by
  rw [row_dia, bottom_row_vector_mirabolic_fixed]

theorem exists_section (ξ : NZ) : ∃ γ : GL (Fin 2) ℚ, e0 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ) = ξ.1 := by
  obtain ⟨ξ, hξ⟩ := ξ
  by_cases h1 : ξ 1 = 0
  · have h0 : ξ 0 ≠ 0 := by
      intro h0
      apply hξ
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; ξ 0, ξ 1] (by simpa [Matrix.det_fin_two] using h0), ?_⟩
    ext i
    fin_cases i <;> simp [e0, GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero !![1, 0; ξ 0, ξ 1] (by simpa [Matrix.det_fin_two] using h1), ?_⟩
    ext i
    fin_cases i <;> simp [e0, GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem exists_pp (q : GL (Fin 2) ℚ) (hq : e0 ᵥ* (q : Matrix (Fin 2) (Fin 2) ℚ) = e0) :
    ∃ α b, q = pp α b := by
  have h10 : (q : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
    have := congrFun hq 0
    simpa [e0, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have h11 : (q : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 := by
    have := congrFun hq 1
    simpa [e0, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have hd : (q : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 q.isUnit
    exact this.ne_zero
  have h00 : (q : Matrix (Fin 2) (Fin 2) ℚ) 0 0 ≠ 0 := by
    intro h
    apply hd
    simp [Matrix.det_fin_two, h, h10]
  refine ⟨Units.mk0 _ h00, (q : Matrix (Fin 2) (Fin 2) ℚ) 0 1 / (q : Matrix (Fin 2) (Fin 2) ℚ) 0 0, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pp, dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, h00, mul_div_cancel₀]

theorem pp_inj {α α' : ℚˣ} {b b' : ℚ} (h : pp α b = pp α' b') : α = α' ∧ b = b' := by
  have h1 := congrArg (fun q : GL (Fin 2) ℚ => (q : Matrix (Fin 2) (Fin 2) ℚ) 0 0) h
  have h2 := congrArg (fun q : GL (Fin 2) ℚ => (q : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
  simp [pp, dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
  have hα : α = α' := Units.ext h1
  subst hα
  exact ⟨rfl, by simpa using h2⟩

instance countableGL : Countable (GL (Fin 2) ℚ) :=
  have : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u : Matrix (Fin 2) (Fin 2) ℚ)) Units.val_injective

theorem param_bij (γs : NZ → GL (Fin 2) ℚ) (hγ : ∀ ξ, e0 ᵥ* ((γs ξ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = ξ.1) :
    Function.Bijective (fun t : ℚˣ × ℚ × NZ => (γs t.2.2)⁻¹ * pp t.1 t.2.1) := by
  have hinv : ∀ (α : ℚˣ) (b : ℚ), e0 ᵥ* (((pp α b)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = e0 := by
    intro α b
    conv_lhs => rw [← bottom_row_vector_mirabolic_fixed α b]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  constructor
  · rintro ⟨α, b, ξ⟩ ⟨α', b', ξ'⟩ h
    simp only at h
    have h1 : (pp α b)⁻¹ * γs ξ = (pp α' b')⁻¹ * γs ξ' := by
      have := congrArg (·⁻¹) h
      simpa using this
    have h2 : ξ.1 = ξ'.1 := by
      have := congrArg (fun q : GL (Fin 2) ℚ => e0 ᵥ* (q : Matrix (Fin 2) (Fin 2) ℚ)) h1
      simp only [Units.val_mul, ← Matrix.vecMul_vecMul, hinv, hγ] at this
      exact this
    have h3 : ξ = ξ' := Subtype.ext h2
    subst h3
    obtain ⟨rfl, rfl⟩ := pp_inj (mul_left_cancel h)
    rfl
  · intro γ
    have hne : e0 ᵥ* ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := by
      intro h
      have h' : e0 = 0 := by
        have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) h
        simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one, Matrix.zero_vecMul] at this
        exact this
      have := congrFun h' 1
      simp [e0] at this
    set ξ : NZ := ⟨_, hne⟩ with hξ
    have hq : e0 ᵥ* ((γs ξ * γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = e0 := by
      rw [Units.val_mul, ← Matrix.vecMul_vecMul, hγ ξ, hξ]
      simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
    obtain ⟨α, b, h⟩ := exists_pp _ hq
    refine ⟨⟨α, b, ξ⟩, ?_⟩
    simp only
    rw [← h]
    group

theorem continuous_unipotentGL2 : Continuous (uni2 : 𝔸[ℚ] → G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop
  · change Continuous fun x : 𝔸[ℚ] => (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagGL2 : Continuous (fun p : Jd × Jd => (dg2 p.1 p.2 : G2)) := by
  have h1 : Continuous fun p : Jd × Jd => ((p.1 : Jd) : 𝔸[ℚ]) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun p : Jd × Jd => ((p.2 : Jd) : 𝔸[ℚ]) := Units.continuous_val.comp continuous_snd
  have h3 : Continuous fun p : Jd × Jd => ((p.1⁻¹ : Jd) : 𝔸[ℚ]) :=
    Units.continuous_val.comp (continuous_fst.inv)
  have h4 : Continuous fun p : Jd × Jd => ((p.2⁻¹ : Jd) : 𝔸[ℚ]) :=
    Units.continuous_val.comp (continuous_snd.inv)
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> first | exact h1 | exact h2 | fun_prop
  · change Continuous fun p : Jd × Jd => (!![((p.1⁻¹ : Jd) : 𝔸[ℚ]), 0; 0, ((p.2⁻¹ : Jd) : 𝔸[ℚ])] : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact h3 | exact h4 | fun_prop

instance secondCountable_adelic_GL2 : SecondCountableTopology G2 := by
  have h2 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) 𝔸[ℚ])).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem continuous_pt {Y : Type*} [TopologicalSpace Y] {x : Y → 𝔸[ℚ]} {a z : Y → Jd} {κ : Y → G2}
    (hx : Continuous x) (ha : Continuous a) (hz : Continuous z) (hκ : Continuous κ) :
    Continuous fun y => pt (x y) (a y) (z y) (κ y) := by
  unfold pt
  have h1 : Continuous fun y => (uni2 (x y) : G2) := continuous_unipotentGL2.comp hx
  have h2 : Continuous fun y => (dg2 (a y) 1 : G2) := continuous_diagGL2.comp (ha.prodMk continuous_const)
  have h3 : Continuous fun y => (dg2 (z y) (z y) : G2) := continuous_diagGL2.comp (hz.prodMk hz)
  exact ((h1.mul h2).mul h3).mul hκ

theorem continuous_row (ξ : Fin 2 → ℚ) : Continuous (row ξ) := by
  unfold Ad3.R.row
  exact Continuous.matrix_vecMul continuous_const Units.continuous_val

theorem md_pri (α : ℚˣ) : md (pri α) = 1 := by
  have : pri α = IdeleGroup.diagonal ℚ α := rfl
  simp [md, this, IdeleGroup.ideleModule_diagonal]

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem lintegral_part {X ι : Type*} [MeasurableSpace X] [Countable ι] (m : Measure X) {S : Set X}
    (hS : MeasurableSet S) (T : ι → X ≃ᵐ X) (hT : ∀ i, MeasurePreserving (T i) m m)
    (hu : ∀ x, ∃! i, T i x ∈ S) (K : X → ℝ≥0∞) :
    ∫⁻ x, K x ∂m = ∑' i, ∫⁻ y in S, K ((T i).symm y) ∂m := by
  have hU : (⋃ i, (T i) ⁻¹' S) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨i, hi, -⟩ := hu x
    exact ⟨i, hi⟩
  have hd : Pairwise (Function.onFun Disjoint fun i => (T i) ⁻¹' S) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hi hj => hij ?_
    exact (hu x).unique hi hj
  calc ∫⁻ x, K x ∂m = ∫⁻ x in ⋃ i, (T i) ⁻¹' S, K x ∂m := by rw [hU, Measure.restrict_univ]
    _ = ∑' i, ∫⁻ x in (T i) ⁻¹' S, K x ∂m := lintegral_iUnion (fun i => (T i).measurable hS) hd K
    _ = _ := tsum_congr fun i => by
      have := (hT i).setLIntegral_comp_preimage_emb (T i).measurableEmbedding (fun y => K ((T i).symm y)) S
      simpa using this

theorem lintegral_cut_a {𝓓 : Set Jd} (hD : MeasurableSet 𝓓) (hu : ∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓)
    (K : Jd → ℝ≥0∞) :
    ∫⁻ a, K a ∂ideleMeasure ℚ = ∑' α : ℚˣ, ∫⁻ a in 𝓓, K (pri α * a) ∂ideleMeasure ℚ := by
  rw [lintegral_part (ideleMeasure ℚ) hD (fun α : ℚˣ => MeasurableEquiv.mulLeft (pri α))
    (fun α => measurePreserving_mul_left _ _) hu K, ← (Equiv.inv ℚˣ).tsum_eq]
  refine tsum_congr fun α => ?_
  simp [pri, map_inv]

theorem map_scale (α : ℚˣ) : MeasurePreserving (fun x : 𝔸[ℚ] => pri α • x) (adeleMeasure ℚ) (adeleMeasure ℚ) := by
  refine ⟨(continuous_const_smul _).measurable, ?_⟩
  rw [map_smul_adeleMeasure]
  have : (IdeleGroup.ideleModule ℚ (pri α) : ℝ) = 1 := md_pri α
  simp [this]

theorem lintegral_adeles_rational_translates (α : ℚˣ) (K : 𝔸[ℚ] → ℝ≥0∞) :
    ∫⁻ x, K x ∂adeleMeasure ℚ =
      ∑' b : ℚ, ∫⁻ x in fundamentalSet ℚ, K ((pri α : 𝔸[ℚ]) * (x + algebraMap ℚ 𝔸[ℚ] b)) ∂adeleMeasure ℚ := by
  have h1 : ∫⁻ x, K x ∂adeleMeasure ℚ = ∫⁻ x, K ((pri α : 𝔸[ℚ]) * x) ∂adeleMeasure ℚ :=
    ((map_scale α).lintegral_comp_emb (Homeomorph.smul (pri α)).measurableEmbedding K).symm
  rw [h1, lintegral_part (adeleMeasure ℚ) (measurableSet_fundamentalSet ℚ)
    (fun b : ℚ => MeasurableEquiv.addRight (-algebraMap ℚ 𝔸[ℚ] b))
    (fun b => measurePreserving_add_right _ _) ?_ (fun x => K ((pri α : 𝔸[ℚ]) * x))]
  · refine tsum_congr fun b => ?_
    simp [sub_eq_add_neg]
  · intro x
    simpa [sub_eq_add_neg] using existsUnique_sub_mem_fundamentalSet ℚ x

def wt (a : Jd) : ℝ≥0∞ := ENNReal.ofReal (md a)⁻¹

theorem measurable_md : Measurable md :=
  (continuous_subtype_val.comp IdeleGroup.continuous_ideleModule).measurable

theorem measurable_wt : Measurable wt := (measurable_md.inv).ennreal_ofReal

theorem wt_ne_zero (a : Jd) : wt a ≠ 0 := by
  have := inv_pos.2 (md_pos a)
  simpa [wt] using this

theorem wt_pri_mul (α : ℚˣ) (a : Jd) : wt (pri α * a) = wt a := by
  simp [wt, md_mul, md_pri]

theorem measurable_pt_full {F : G2 → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun q : ((KA × Jd) × Jd) × 𝔸[ℚ] => F (pt q.2 q.1.2 q.1.1.2 q.1.1.1.1) * wt q.1.2 := by
  have h : Continuous fun q : ((KA × Jd) × Jd) × 𝔸[ℚ] => pt q.2 q.1.2 q.1.1.2 q.1.1.1.1 :=
    continuous_pt continuous_snd continuous_fst.snd continuous_fst.fst.snd
      (continuous_subtype_val.comp continuous_fst.fst.fst)
  exact (hF.comp h.measurable).mul (measurable_wt.comp (measurable_fst.snd))

theorem cut {𝓓 : Set Jd} (hD : MeasurableSet 𝓓) (hu : ∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓)
    {F : G2 → ℝ≥0∞} (hF : Measurable F) (z : Jd) (κ : KA) :
    ∫⁻ a, ∫⁻ x, F (pt x a z κ.1) * wt a ∂adeleMeasure ℚ ∂ideleMeasure ℚ =
      ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
        (∑' α : ℚˣ, ∑' b : ℚ, F (dia2 (pp α b) * pt x a z κ.1)) * wt a ∂adeleMeasure ℚ ∂ideleMeasure ℚ := by
  have hY : ∀ (α : ℚˣ) (b : ℚ), Measurable fun q : Jd × 𝔸[ℚ] =>
      F (dia2 (pp α b) * pt q.2 q.1 z κ.1) * wt q.1 := by
    intro α b
    have h0 : Continuous fun q : Jd × 𝔸[ℚ] => pt q.2 q.1 z κ.1 :=
      continuous_pt continuous_snd continuous_fst continuous_const continuous_const
    have h : Continuous fun q : Jd × 𝔸[ℚ] => dia2 (pp α b) * pt q.2 q.1 z κ.1 := continuous_const.mul h0
    exact (hF.comp h.measurable).mul (measurable_wt.comp measurable_fst)
  have hYx : ∀ (α : ℚˣ) (b : ℚ) (a : Jd), Measurable fun x : 𝔸[ℚ] =>
      F (dia2 (pp α b) * pt x a z κ.1) * wt a := fun α b a =>
    (hF.comp (continuous_const.mul (continuous_pt continuous_id continuous_const continuous_const
      continuous_const)).measurable).mul_const _
  have hYa : ∀ (α : ℚˣ) (b : ℚ), Measurable fun a : Jd => ∫⁻ x in fundamentalSet ℚ,
      F (dia2 (pp α b) * pt x a z κ.1) * wt a ∂adeleMeasure ℚ := fun α b =>
    (hY α b).lintegral_prod_right'
  rw [lintegral_cut_a hD hu]
  have h1 : ∀ (α : ℚˣ) (a : Jd), ∫⁻ x, F (pt x (pri α * a) z κ.1) * wt (pri α * a) ∂adeleMeasure ℚ =
      ∑' b : ℚ, ∫⁻ x in fundamentalSet ℚ, F (dia2 (pp α b) * pt x a z κ.1) * wt a ∂adeleMeasure ℚ := by
    intro α a
    rw [lintegral_adeles_rational_translates α]
    refine tsum_congr fun b => lintegral_congr fun x => ?_
    rw [mirabolic_mul_iwasawa_coordinates, wt_pri_mul]
  simp only [h1]
  have h2 : ∀ a : Jd, ∫⁻ x in fundamentalSet ℚ,
      (∑' α : ℚˣ, ∑' b : ℚ, F (dia2 (pp α b) * pt x a z κ.1)) * wt a ∂adeleMeasure ℚ =
      ∑' α : ℚˣ, ∑' b : ℚ, ∫⁻ x in fundamentalSet ℚ,
        F (dia2 (pp α b) * pt x a z κ.1) * wt a ∂adeleMeasure ℚ := by
    intro a
    simp only [← ENNReal.tsum_mul_right]
    rw [lintegral_tsum fun α => (Measurable.ennreal_tsum fun b => hYx α b a).aemeasurable]
    refine tsum_congr fun α => ?_
    rw [lintegral_tsum fun b => (hYx α b a).aemeasurable]
  simp only [h2]
  rw [lintegral_tsum fun α => (Measurable.ennreal_tsum fun b => hYa α b).aemeasurable]

theorem null_pull {μ : Measure G2} {mK : Measure KA} {C : NNReal} [SFinite mK] (hC : Coord μ mK C)
    {N : Set G2} (hN : MeasurableSet N) (h0 : μ N = 0) :
    ∀ᵐ κ : KA ∂mK, ∀ᵐ z ∂ideleMeasure ℚ, ∀ᵐ a ∂ideleMeasure ℚ, ∀ᵐ x ∂adeleMeasure ℚ, pt x a z κ.1 ∉ N := by
  set F : G2 → ℝ≥0∞ := N.indicator 1 with hFdef
  have hF : Measurable F := measurable_one.indicator hN
  have h4 := measurable_pt_full hF
  have h3 := h4.lintegral_prod_right' (ν := adeleMeasure ℚ)
  have h2 := h3.lintegral_prod_right' (ν := ideleMeasure ℚ)
  have h1 := h2.lintegral_prod_right' (ν := ideleMeasure ℚ)
  have hz : ∫⁻ κ : KA, ∫⁻ z, ∫⁻ a, ∫⁻ x, F (pt x a z κ.1) * wt a
      ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK = 0 := by
    have hh := hC.2 F hF
    have hl : ∫⁻ g, F g ∂μ = 0 := by
      rw [hFdef, lintegral_indicator_one hN, h0]
    rw [hl] at hh
    have := (mul_eq_zero.1 hh.symm).resolve_left (by simpa using hC.1)
    exact this
  rw [lintegral_eq_zero_iff h1] at hz
  filter_upwards [hz] with κ hκ
  have hκ' := (lintegral_eq_zero_iff (h2.comp measurable_prodMk_left)).1 hκ
  filter_upwards [hκ'] with z hz'
  have hz'' := (lintegral_eq_zero_iff (h3.comp (measurable_prodMk_left (x := (κ, z))))).1 hz'
  filter_upwards [hz''] with a ha
  have ha' := (lintegral_eq_zero_iff (h4.comp (measurable_prodMk_left (x := ((κ, z), a))))).1 ha
  filter_upwards [ha'] with x hx hmem
  have h := (mul_eq_zero.1 hx).resolve_right (wt_ne_zero a)
  simp [hFdef, hmem] at h

theorem ae_unique {μ : Measure G2} {𝓕 : Set G2}
    (fd : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ) :
    ∀ᵐ g ∂μ, ∑' γ : GL (Fin 2) ℚ, 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 γ * g) = 1 := by
  have hcount : Countable (AdelicGLn.diagonal ℚ 2).range := by
    have : (Set.range (AdelicGLn.diagonal ℚ 2)).Countable := Set.countable_range _
    exact this.to_subtype
  have hdis : ∀ᵐ x ∂μ, ∀ g g' : (AdelicGLn.diagonal ℚ 2).range, g ≠ g' → ¬ (x ∈ g • 𝓕 ∧ x ∈ g' • 𝓕) := by
    rw [ae_all_iff]
    intro g
    rw [ae_all_iff]
    intro g'
    by_cases h : g = g'
    · exact Filter.Eventually.of_forall fun _ hne => absurd h hne
    · have h0 : μ (g • 𝓕 ∩ g' • 𝓕) = 0 := fd.aedisjoint h
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx _
      exact hx
  filter_upwards [fd.ae_covers, hdis] with g ⟨⟨_, γ₀, rfl⟩, h₀⟩ hd
  have hdia : Function.Injective fun γ : GL (Fin 2) ℚ => dia2 γ := by
    intro γ γ' h
    apply Units.ext
    ext i j
    have h1 := congrArg (fun q : G2 => (q : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i j) h
    simp only [AdelicGLn.diagonal] at h1
    exact AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (by simpa using h1)
  have hinj : ∀ {γ γ' : GL (Fin 2) ℚ}, dia2 γ * g ∈ 𝓕 → dia2 γ' * g ∈ 𝓕 → γ = γ' := by
    intro γ γ' h h'
    by_contra hne
    have hne' : (⟨dia2 γ, γ, rfl⟩ : (AdelicGLn.diagonal ℚ 2).range)⁻¹ ≠ (⟨dia2 γ', γ', rfl⟩ : (AdelicGLn.diagonal ℚ 2).range)⁻¹ := by
      intro he
      exact hne (hdia (congrArg Subtype.val (inv_injective he)))
    refine hd _ _ hne' ⟨?_, ?_⟩
    · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact h
    · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact h'
  have h₁ : dia2 γ₀ * g ∈ 𝓕 := h₀
  rw [tsum_eq_single γ₀ fun γ hne => Set.indicator_of_notMem (fun hm => hne (hinj hm h₁)) _,
    Set.indicator_of_mem h₁]
  rfl

section Unfold

variable {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℝ≥0∞} {Φ : (Fin 2 → 𝔸[ℚ]) → ℝ≥0∞}
  [μ.IsMulLeftInvariant]

theorem unfold_step (hF : MeasurableSet 𝓕) (hH : Measurable H) (hL : LInv H) (hΦ : Measurable Φ)
    (γs : NZ → GL (Fin 2) ℚ)
    (hγ : ∀ ξ, e0 ᵥ* ((γs ξ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = ξ.1) :
    ∫⁻ g in 𝓕, H g * ∑' ξ : NZ, Φ (row ξ.1 g) ∂μ =
      ∫⁻ g, (H g * Φ (row e0 g)) * ∑' ξ : NZ, 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g) ∂μ := by
  set f : G2 → ℝ≥0∞ := fun g => H g * Φ (row e0 g) with hf
  have hmf : Measurable f := hH.mul (hΦ.comp (continuous_row e0).measurable)
  have hmul : ∀ h : G2, Measurable fun g : G2 => h * g := fun h => measurable_const_mul h
  have hind : Measurable (𝓕.indicator (1 : G2 → ℝ≥0∞)) := measurable_one.indicator hF
  have h1 : ∀ (ξ : NZ) (g : G2), H g * Φ (row ξ.1 g) = f (dia2 (γs ξ) * g) := by
    intro ξ g
    simp only [hf]
    rw [hL, row_dia, hγ]
  have h2 : ∀ ξ : NZ, ∫⁻ g in 𝓕, f (dia2 (γs ξ) * g) ∂μ =
      ∫⁻ g, f g * 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g) ∂μ := by
    intro ξ
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun g => f g * 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g)) (dia2 (γs ξ)),
      ← lintegral_indicator hF]
    refine lintegral_congr fun g => ?_
    have hc : dia2 (γs ξ)⁻¹ * (dia2 (γs ξ) * g) = g := by
      change AdelicGLn.diagonal ℚ 2 (γs ξ)⁻¹ * (AdelicGLn.diagonal ℚ 2 (γs ξ) * g) = g
      rw [map_inv, inv_mul_cancel_left]
    rw [hc]
    by_cases hg : g ∈ 𝓕 <;> simp [hg]
  have h3 : ∀ ξ : NZ, Measurable fun g => f (dia2 (γs ξ) * g) := fun ξ => hmf.comp (hmul _)
  have h4 : ∀ ξ : NZ, Measurable fun g => f g * 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g) :=
    fun ξ => hmf.mul (hind.comp (hmul _))
  calc ∫⁻ g in 𝓕, H g * ∑' ξ : NZ, Φ (row ξ.1 g) ∂μ
      = ∫⁻ g in 𝓕, ∑' ξ : NZ, f (dia2 (γs ξ) * g) ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun ξ => h1 ξ g
    _ = ∑' ξ : NZ, ∫⁻ g in 𝓕, f (dia2 (γs ξ) * g) ∂μ := lintegral_tsum fun ξ => (h3 ξ).aemeasurable
    _ = ∑' ξ : NZ, ∫⁻ g, f g * 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g) ∂μ := tsum_congr h2
    _ = ∫⁻ g, ∑' ξ : NZ, f g * 𝓕.indicator (1 : G2 → ℝ≥0∞) (dia2 (γs ξ)⁻¹ * g) ∂μ :=
        (lintegral_tsum fun ξ => (h4 ξ).aemeasurable).symm
    _ = _ := lintegral_congr fun g => ENNReal.tsum_mul_left

end Unfold

theorem unfolding_mirabolic_cosets : Ad3.R.G2b := by
  intro μ 𝓕 mK 𝓓 C h0 hC H Φ hH hL hΦ
  choose γs hγ using exists_section
  haveI := h0.haar
  haveI := h0.probK
  set ind : G2 → ℝ≥0∞ := 𝓕.indicator 1 with hind
  set bet : G2 → ℝ≥0∞ := fun g => ∑' ξ : NZ, ind (dia2 (γs ξ)⁻¹ * g) with hbet
  set f : G2 → ℝ≥0∞ := fun g => H g * Φ (row e0 g) with hf
  have hmf : Measurable f := hH.mul (hΦ.comp (continuous_row e0).measurable)
  have hmul : ∀ h : G2, Measurable fun g : G2 => h * g := fun h => measurable_const_mul h
  have hmind : Measurable ind := measurable_one.indicator h0.meas
  have hmbet : Measurable bet := Measurable.ennreal_tsum fun ξ => hmind.comp (hmul _)

  have hB : ∀ᵐ g ∂μ, ∑' α : ℚˣ, ∑' b : ℚ, bet (dia2 (pp α b) * g) = 1 := by
    filter_upwards [ae_unique h0.fd] with g hg
    rw [← (Equiv.ofBijective _ (param_bij γs hγ)).tsum_eq] at hg
    rw [ENNReal.tsum_prod'] at hg
    simp only [ENNReal.tsum_prod', Equiv.ofBijective_apply, map_mul, mul_assoc] at hg
    simpa only [hbet] using hg
  set N : Set G2 := {g | ∑' α : ℚˣ, ∑' b : ℚ, bet (dia2 (pp α b) * g) ≠ 1} with hN
  have hmN : MeasurableSet N := by
    have : Measurable fun g : G2 => ∑' α : ℚˣ, ∑' b : ℚ, bet (dia2 (pp α b) * g) :=
      Measurable.ennreal_tsum fun α => Measurable.ennreal_tsum fun b => hmbet.comp (hmul _)
    exact (this (measurableSet_singleton 1)).compl
  have hN0 : μ N = 0 := hB
  rw [unfold_step h0.meas hH hL hΦ γs hγ]
  refine (hC.2 (fun g => f g * bet g) (hmf.mul hmbet)).trans ?_
  congr 1
  apply lintegral_congr_ae
  filter_upwards [null_pull hC hmN hN0] with κ hκ
  apply lintegral_congr_ae
  filter_upwards [hκ] with z hz
  have hcut := cut (F := fun g => f g * bet g) h0.measD h0.uniqD (hmf.mul hmbet) z κ
  simp only [wt] at hcut
  refine hcut.trans ?_
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hz] with a ha
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae ha] with x hx
  have hx' : ∑' α : ℚˣ, ∑' b : ℚ, bet (dia2 (pp α b) * pt x a z κ.1) = 1 := by
    by_contra hne
    exact hx hne
  have hfp : ∀ (α : ℚˣ) (b : ℚ), f (dia2 (pp α b) * pt x a z κ.1) = f (pt x a z κ.1) := by
    intro α b
    simp only [hf]
    rw [hL, bottom_row_mirabolic_invariance]
  simp only [hfp, ENNReal.tsum_mul_left, hx', mul_one]
  simp only [hf, bottom_row_iwasawa_coordinates]

end GlobalTheory.CompanionTheory.RSUnfold

end
