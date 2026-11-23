import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RconvSlice
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.DixmierMalliavin

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem dm_induction {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (P : TI K n → Prop) (h0 : P 0)
    (hc : ∀ β₁ β₂ : TI K n, SmoothT β₁ → P (conv ν β₁ β₂))
    (ha : ∀ β β' : TI K n, SmoothT β → SmoothT β' → P β → P β' → P (β + β'))
    (β : TI K n) (hβ : SmoothT β) : P β := by
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => β g) hβ β.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  have h0s : SmoothT (0 : TI K n) :=
    (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
  have key : ∀ s : Finset (Fin N), SmoothT (∑ i ∈ s, conv ν (a i) (b i)) ∧ P (∑ i ∈ s, conv ν (a i) (b i)) ∧
      ∀ x, (∑ i ∈ s, conv ν (a i) (b i)) x = ∑ i ∈ s, groupConv ν (φ i) (ψ i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using h0s, by simpa using h0, fun x => by simp⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hs := (UpperTheory.ConvolutionTheory.Tf.lactConv K n ν (a i) (b i) (has i)).1
      obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hs
      refine ⟨(h6 _ ih.1).1, ha _ _ hs ih.1 (hc _ _ (has i)) ih.2.1, fun x => ?_⟩
      rw [Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih.2.2, conv_apply]
      rfl
  have eβ : β = ∑ i, conv ν (a i) (b i) := by
    ext x
    rw [(key Finset.univ).2.2 x, ← Finset.sum_apply, ← e]
  rw [eβ]
  exact (key Finset.univ).2.1

private theorem lift_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (β β' : TI K n) (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne K n) μ (tens (β + β') e) φ) =
      liftOne (rconv (rationalGLOne K n) μ (tens β e) φ) + liftOne (rconv (rationalGLOne K n) μ (tens β' e) φ) := by
  funext g
  rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).2.2.1 β']
  simp only [liftOne, Pi.add_apply, rconv]
  rw [← integral_add (integrable_rconv _ μ _ φ _) (integrable_rconv _ μ _ φ _)]
  simp only [CompactlySupportedContinuousMap.add_apply, add_mul]

private theorem lift_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne K n) μ (tens (0 : TI K n) e) φ) = 0 := by
  have := lift_add hn μ 0 0 e φ
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem UpperTheory.liftOne_rconv_mem_archSmooth_and_envelopingAction_eq :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], Compat μ ν m →
          ∀ (β : TI K n) (e : TF K n), SmoothT β → ∀ φ : LL μ,
          ∃ h : liftOne (rconv (rationalGLOne K n) μ (tens β e) φ) ∈ archSmooth K n, ∀ u : UC K n,
            (uAct u ⟨_, h⟩ : AdelicGLn.AdelicGL K n → ℂ) = liftOne (rconv (rationalGLOne K n) μ (tens (lact u β) e) φ) := by
  intro K _ _ n hn μ _ ν _ m _ hC β e hβ φ
  have pack : ∀ (γ : TI K n) (F : archSmooth K n), liftOne (rconv (rationalGLOne K n) μ (tens γ e) φ) = F →
      (∀ u : UC K n, (uAct u F : AdelicGLn.AdelicGL K n → ℂ) =
        liftOne (rconv (rationalGLOne K n) μ (tens (lact u γ) e) φ)) →
      ∃ h : liftOne (rconv (rationalGLOne K n) μ (tens γ e) φ) ∈ archSmooth K n, ∀ u : UC K n,
        (uAct u ⟨_, h⟩ : AdelicGLn.AdelicGL K n → ℂ) = liftOne (rconv (rationalGLOne K n) μ (tens (lact u γ) e) φ) := by
    intro γ F hF hu
    refine ⟨hF ▸ F.2, fun u => ?_⟩
    rw [← hu u]
    congr 2
    exact Subtype.ext hF
  refine dm_induction ν (fun γ => ∃ h : liftOne (rconv (rationalGLOne K n) μ (tens γ e) φ) ∈ archSmooth K n, ∀ u : UC K n,
        (uAct u ⟨_, h⟩ : AdelicGLn.AdelicGL K n → ℂ) = liftOne (rconv (rationalGLOne K n) μ (tens (lact u γ) e) φ))
    ?_ ?_ ?_ β hβ
  · refine pack 0 0 (lift_zero hn μ e φ) fun u => ?_
    have h0s : SmoothT (0 : TI K n) :=
      (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ h0s
    have h := (h6 0 h0s).2 u
    rw [add_zero] at h
    rw [left_eq_add.1 h, lift_zero hn, map_zero, Submodule.coe_zero]
  · intro β₁ β₂ h₁
    obtain ⟨h, hu⟩ := (UpperTheory.ConvolutionTheory.Tf.rconvSlice K n hn μ ν m hC β₁ β₂ e φ h₁).2
    refine ⟨h, fun u => ?_⟩
    rw [hu u, (UpperTheory.ConvolutionTheory.Tf.lactConv K n ν β₁ β₂ h₁).2.1 u]
  · rintro γ γ' hγ hγ' ⟨h, hu⟩ ⟨h', hu'⟩
    refine pack _ (⟨_, h⟩ + ⟨_, h'⟩) (lift_add hn μ γ γ' e φ) fun u => ?_
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hγ
    rw [(h6 γ' hγ').2 u, lift_add hn, map_add, Submodule.coe_add, hu u, hu' u]
