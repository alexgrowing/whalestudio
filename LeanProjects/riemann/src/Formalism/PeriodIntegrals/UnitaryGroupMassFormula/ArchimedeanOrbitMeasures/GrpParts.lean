import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Matrix Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem continuous_matExp (n : ℕ) : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  open scoped Norms.Operator in NormedSpace.exp_continuous

theorem continuous_expU {n : ℕ} (ε : Fin n → Bool) {Y : Type} [TopologicalSpace Y]
    (f : Y → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (hL : ∀ y, (f y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * f y = 0) : Continuous (fun y => expU ε (f y)) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : (Units.val ∘ Subtype.val ∘ fun y => expU ε (f y)) = fun y => NormedSpace.exp (f y) :=
      funext fun y => expU_val ε _ (hL y)
    rw [e]
    exact (continuous_matExp n).comp hf
  · have e : (fun x => ((((Subtype.val ∘ fun y => expU ε (f y)) x)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun y => NormedSpace.exp (-f y) := by
      funext y
      apply Units.inv_eq_of_mul_eq_one_right
      show (((expU ε (f y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        NormedSpace.exp (-f y) = 1
      rw [expU_val ε _ (hL y), ← Matrix.exp_add_of_commute (f y) (-f y) (Commute.neg_right (Commute.refl (f y))), add_neg_cancel,
        NormedSpace.exp_zero]
    rw [e]
    exact (continuous_matExp n).comp hf.neg

theorem continuous_kap0_of_lieCompl {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (hL : LieCompl X S L) : Continuous (kap0 X hb c L) := by
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hg : Continuous (fun x => ((fun v => expU (X.B.I.ε v) (L x v)) : X.B.I.Ginf)) :=
    continuous_pi fun v => continuous_expU _ (fun x => L x v) ((continuous_apply v).comp hLc)
      (fun x => (hL.1 x v).1)
  exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul hg).mul continuous_const)

def chiOf {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {η : Type}
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (y : EuclideanSpace ℝ η) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L₁ y v)) * c⁻¹)

def BlockLie {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {η : Type}
    [Fintype η]
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ y v, (L₁ y v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L₁ y v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → L₁ y v i j = 0) ∧
  (∀ y, ∑ v, ∑ i, ∑ j, ‖L₁ y v i j‖ ^ 2 = ‖y‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ y, L₁ y = M

def BlockEx : Prop := ∀ {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)),
    ∃ (η : Type) (_ : Fintype η)
      (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      BlockLie X S L₁

def StdCtx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) : Prop :=
  (∃ ψ : AddChar (AF X.B.I.F) ℂ, ∃ hT μinf νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf) ∧
    StdConj X hb u' c S ∧ LieCompl X S L ∧ BlockLie X S L₁

def ChiStab : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')

def GrpDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        X.measG.μGinf ((fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

def GrpHaarH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ hS : ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'),
    ∃ (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) (r : ℝ)
      (e : EuclideanSpace ℝ η → ℝ),
      ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧
      (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) ∧
      ∀ s, 0 < s → s ≤ r → ν ((fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s) =
        ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)

def GrpInj : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r,
        (kap0 X hb c L a)⁻¹ * kap0 X hb c L b ∈
          MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
      Set.InjOn (chiOf X hb c L₁) (ball 0 r)

theorem grpPiecesStd_of (h0 : BlockEx) (hS : ChiStab) (hD : GrpDens) (hH : GrpHaarH) (hI : GrpInj) :
    GrpPiecesStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  obtain ⟨η, hη, L₁, hB⟩ := h0 X S
  have ctx : StdCtx X u' hb c S L L₁ := ⟨⟨ψ, hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩
  have hst := hS X u' hb c S L L₁ ctx
  obtain ⟨r1, hr1, d, hdc, hd0, hdens⟩ := hD X u' hb c S L L₁ ctx
  obtain ⟨ν, r2, e, hL', hSF, h0', hf, hr2, hec, he0, hvol, hνd⟩ := hH X u' hb c S L L₁ ctx hst
  obtain ⟨r3, hr3, hinj, hχi⟩ := hI X u' hb c S L L₁ ctx
  have hr : 0 < min r1 (min r2 r3) := lt_min hr1 (lt_min hr2 hr3)
  have h1 : min r1 (min r2 r3) ≤ r1 := min_le_left _ _
  have h2 : min r1 (min r2 r3) ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min r1 (min r2 r3) ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  have hχc : Continuous (fun y => (⟨chiOf X hb c L₁ y, hst y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) := by
    apply Continuous.subtype_mk
    have hLc : Continuous L₁ := L₁.continuous_of_finiteDimensional
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_expU _ (fun y => L₁ y v) ((continuous_apply v).comp hLc) (fun y => (hB.1 y v).1))).mul
        continuous_const)
  have hgpos : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := Finset.prod_pos fun v _ => (hP.2.2.2.1 v).2
  have hdet1 : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
    simp [ContinuousLinearMap.det]
  refine ⟨η, hη, fun y => ⟨chiOf X hb c L₁ y, hst y⟩, min r1 (min r2 r3),
    fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2, ball 0 (min r1 (min r2 r3)), d, id,
    fun _ => ContinuousLinearMap.id ℝ _, e, ν, hL', hSF, h0', hf, hr,
    (continuous_kap0_of_lieCompl X hb c S L hL).continuousOn, hχc.continuousOn, ?_, ?_, ?_, ?_, Set.injOn_id _, ?_, ?_, ?_,
    continuousAt_id, ?_, hdc, hec, he0, ?_, ?_⟩
  · intro a ha b hb' hab
    exact hχi (ball_subset_ball h3 ha) (ball_subset_ball h3 hb') (congrArg Subtype.val hab)
  · intro a ha b hb' hm
    exact hinj a (ball_subset_ball h3 ha) b (ball_subset_ball h3 hb') hm
  · intro A hA hAm
    exact hdens A (hA.trans (ball_subset_ball h1)) hAm
  · intro p _
    exact hasFDerivWithinAt_id p _
  · rw [Set.image_id]
  · intro p _
    rfl
  · intro s hs hsr
    exact hνd s hs (hsr.trans h2)
  · simp only [hdet1]
    exact continuousAt_const
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0]
    exact hgpos
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0, gVal, ← hvol]
    ring

set_option backward.isDefEq.respectTransparency false in

theorem exp_mul_of_mul_eq_zero {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℂ) (hMP : M * P = 0) :
    NormedSpace.exp M * P = P := by
  open scoped Norms.Operator in
  have hs : Summable (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • M ^ k) := NormedSpace.expSeries_summable' (𝕂 := ℚ) M
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_right P, tsum_eq_single 0]
  · simp
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [smul_mul_assoc, pow_succ, Matrix.mul_assoc, hMP, Matrix.mul_zero, smul_zero]

theorem exp_block_col {n : ℕ} (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    NormedSpace.exp M j i = if j = i then 1 else 0 := by
  have hMP : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0 := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b ∈ S
    · simp [hb]
    · simp [hb, hM a b (Or.inr hb)]
  have h := congrFun (congrFun (exp_mul_of_mul_eq_zero M _ hMP) j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at h
  simp only [hi, if_false, mul_one] at h
  rw [h]
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

theorem chiStab' : ChiStab := by
  intro D X u' hb c S ι η _ _ L L₁ ctx y
  unfold chiOf
  refine (ctx.2.1.2 _).2 fun v i hi j => ?_
  show (((expU (X.B.I.ε v) (L₁ y v) : Formalism.REAL.UJ (X.B.I.ε v)) :
    (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) j i = _
  rw [expU_val _ _ (ctx.2.2.2.1 y v).1]
  exact exp_block_col (S v) _ (ctx.2.2.2.1 y v).2 i hi j

end PI.AprimeInfW
