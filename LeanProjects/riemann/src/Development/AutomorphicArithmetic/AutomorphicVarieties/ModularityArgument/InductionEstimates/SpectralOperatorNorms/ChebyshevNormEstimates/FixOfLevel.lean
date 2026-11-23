import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace Pointwise

private theorem fix_of_level {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (D : TypeDat K n) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (hD : D.Level U)
    (hU : U ≤ AdelicGLn.integralFiniteGL K n) (v : LL μ) (hv : D.FixedByTypeProjector μ v) : v ∈ fixF μ U := by
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.1]
  intro u hu
  have key : ∀ u ∈ U, MultiplicityOne.finProj K n u ∈ D.U ∧ (AdelicGLn.prodEquiv K n (MultiplicityOne.finProj K n u : G1 K n)).1 = 1 := by
    intro u hu
    have h1 : ((MultiplicityOne.finProj K n u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u := by
      rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact (hU hu)))]
    have h2 : AdelicGLn.prodEquiv K n (finEmb K n u) = (1, u) := (AdelicGLn.prodEquiv K n).apply_symm_apply _
    have h3 : (AdelicGLn.prodEquiv K n (MultiplicityOne.finProj K n u : G1 K n)).1 = 1 := by rw [h1, h2]
    refine ⟨(hD.1 _ h3).2 ?_, h3⟩
    rw [h1, h2]; exact hu
  set g := MultiplicityOne.finProj K n u with hg
  obtain ⟨hgU, hg1⟩ := key u hu
  have hme : MeasurableEmbedding (fun k : G1 K n => g * k) := measurableEmbedding_mulLeft g
  have hcomp := (D.inv g hgU).integral_comp hme (fun k => D.e k • rightRegularRep (Gam K n) μ k v)
  unfold TypeDat.FixedByTypeProjector at hv
  have hint : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν ∨ v = 0 := by
    by_cases h : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν
    · exact Or.inl h
    · rw [integral_undef h] at hv
      exact Or.inr hv.symm
  rcases hint with hint | h0
  · calc rhoF μ u v = rhoF μ u (∫ k, D.e k • rightRegularRep (Gam K n) μ k v ∂D.ν) := by rw [hv]
      _ = ∫ k, rhoF μ u (D.e k • rightRegularRep (Gam K n) μ k v) ∂D.ν := ((rhoF μ u).integral_comp_comm hint).symm
      _ = ∫ k, D.e (g * k) • rightRegularRep (Gam K n) μ (g * k) v ∂D.ν := by
          refine integral_congr_ae (D.supp.mono fun k hk => ?_)
          show rhoF μ u (D.e k • rightRegularRep (Gam K n) μ k v) = D.e (g * k) • rightRegularRep (Gam K n) μ (g * k) v
          rw [hD.2.2 g hgU hg1 k hk, map_smul, UnitaryRep.map_mul_apply]
          rfl
      _ = v := hcomp.trans hv
  · rw [h0, map_zero]

private theorem proj_absorb {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P e : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P) (he : IsSelfAdjoint e)
    (h1 : ∀ u, e (J u) = J u) (h2 : ∀ u, e (J' u) = J' u) : P * e = P ∧ e * P = P := by
  have hs : ∀ x y, ⟪x, e y⟫_ℂ = ⟪e x, y⟫_ℂ := fun x y => (he.isSymmetric x y).symm
  have a : P * e = P := by
    refine ContinuousLinearMap.ext fun h => ?_
    have : P (e h - h) = 0 := (hP.2.2 _).2 ⟨fun u => by rw [inner_sub_right, hs, h1, sub_self],
      fun u => by rw [inner_sub_right, hs, h2, sub_self]⟩
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨a, ?_⟩
  have := congrArg star a
  rwa [star_mul, he.star_eq, hP.1.star_eq] at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genTk :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (w : Pl E), w ∉ 𝔢.S → ∀ i : Fin (2 + 2),
      (∃ s, Act 𝔵.A'.J (Tsph μ w i) s) ∧ Tsph μ w i ∘L 𝔵.P = 𝔵.P ∘L Tsph μ w i := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 w hw i
  have hc : IsCompact (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) :=
    (AdelicGLn.isCompact_integralFiniteGL E (2 + 2)).of_isClosed_subset (𝔢.U.isClosed_of_isOpen 𝔢.isOpen) 𝔢.le
  have hp' : Pair (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩
  let m : Measure (AdelicGLn.FiniteAdelicGL E (2 + 2)) := Measure.haar
  set x := Cartan.diagPow (w.adicCompletion E) (2 + 2) fun a => if a ≤ i then 1 else 0 with hx
  set T := Hop μ w (GLnLocal.integralGL (w.adicCompletion E) (2 + 2)) x with hT
  obtain ⟨hcomm, e, he, hO⟩ := UpperTheory.ConvolutionTheory.Tf.hopLevel E (2 + 2) μ m w (GLnLocal.integralGL (w.adicCompletion E) (2 + 2)) x 𝔢.U
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) 𝔢.isOpen hc (𝔢.max w hw)
    fun u hu => (mem_maxCompact.1 (finEmb_mem_maxCompact (𝔢.le hu))).2 w
  have hbi : ∀ k ∈ 𝔢.U, ∀ h, e (k * h) = e h ∧ e (h * k) = e h := by
    have hl : ∀ k ∈ 𝔢.U, ∀ h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))),
        k * h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) ∧
        h * k ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) := by
      rintro k hk _ ⟨_, ⟨a, ha, y, hy, rfl⟩, b, hb, rfl⟩
      exact ⟨⟨_, ⟨k * a, 𝔢.U.mul_mem hk ha, y, hy, rfl⟩, b, hb, by simp only [mul_assoc]⟩,
        ⟨_, ⟨a, ha, y, hy, rfl⟩, b * k, 𝔢.U.mul_mem hb hk, by simp only [mul_assoc]⟩⟩
    intro k hk h
    rw [he, he, he]
    by_cases hh : h ∈ (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2))) * {AdelicGLn.localEmbedding w x} * (𝔢.U : Set (AdelicGLn.FiniteAdelicGL E (2 + 2)))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (hl k hk h hh).1, Set.indicator_of_mem (hl k hk h hh).2]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem, Set.indicator_of_notMem]
      · exact ⟨rfl, rfl⟩
      · intro h'
        have := (hl _ (𝔢.U.inv_mem hk) _ h').2
        rw [mul_inv_cancel_right] at this
        exact hh this
      · intro h'
        have := (hl _ (𝔢.U.inv_mem hk) _ h').1
        rw [inv_mul_cancel_left] at this
        exact hh this
  have hfix := (UpperTheory.ConvolutionTheory.Tf.commPrj E (2 + 2) μ 𝔢.U).2.2.2.1
  have f1 : ∀ u, prj (fixF μ 𝔢.U) (𝔵.A.J u) = 𝔵.A.J u := fun u =>
    hfix _ (fix_of_level μ 𝔵.D 𝔢.U 𝔵.level 𝔢.le _ (ctZero E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' u).2.1)
  have f2 : ∀ u, prj (fixF μ 𝔢.U) (𝔵.A'.J u) = 𝔵.A'.J u := fun u =>
    hfix _ (fix_of_level μ 𝔵.D 𝔢.U 𝔵.level 𝔢.le _ (ctZero E μ _ _ _ hp' 𝔵.D _ _ 𝔵.A' 𝔵.A u).2.1)
  have hsa : IsSelfAdjoint (prj (fixF μ 𝔢.U)) := isSelfAdjoint_starProjection _
  obtain ⟨a1, a2⟩ := proj_absorb 𝔵.A.J 𝔵.A'.J 𝔵.P _ 𝔵.isP hsa f1 f2
  have hPc := (finAct E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔢.U 𝔵.level 𝔢.le m e hbi).2 𝔵.P 𝔵.isP
  obtain ⟨s, ⟨u, κ, hκ, hact, hs⟩, -⟩ := (finAct E μ _ _ _ hp' 𝔵.D _ _ 𝔵.A' 𝔵.A 𝔢.U 𝔵.level 𝔢.le m e hbi).1
  have hA : Act 𝔵.A'.J T s := ⟨u, κ, hκ, fun y => by
    rw [← hact y, hO, ContinuousLinearMap.comp_apply, f2], hs⟩
  have hTP : T * 𝔵.P = 𝔵.P * T := by
    rw [hO] at hPc
    have h1 : T * prj (fixF μ 𝔢.U) * 𝔵.P = 𝔵.P * (T * prj (fixF μ 𝔢.U)) := hPc
    rwa [mul_assoc, a2, hcomm.eq, ← mul_assoc, a1] at h1
  refine ⟨⟨_, ((actLaws 𝔵.A'.J).2.2.1 T s hA).2 _⟩, ?_⟩
  unfold Tsph
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  exact congrArg _ hTP
