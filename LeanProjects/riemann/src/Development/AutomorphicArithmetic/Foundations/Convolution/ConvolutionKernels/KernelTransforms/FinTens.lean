import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.LocalTestFunctions.ExistsCompactOpenBiinvariantOfTest
import Development.AutomorphicArithmetic.LocalTestFunctions.LocalOperatorCompRhoLEqOfRightInvariant
import Development.AutomorphicArithmetic.LocalTestFunctions.LocalOperatorCommuteRhoFOfTrivialAtPlace
import Development.AutomorphicArithmetic.LocalTestFunctions.IntegratedRightRegularEqLocalOperator
import Development.AutomorphicArithmetic.LocalTestFunctions.ExistsOpenCompactLevelSubgroup
import Development.AutomorphicArithmetic.LocalTestFunctions.IndicatorLevelEqProdLocalIndicator
import Development.AutomorphicArithmetic.LocalTestFunctions.FinprodLocalEqIndicatorMulProd
import Development.AutomorphicArithmetic.LocalTestFunctions.IndicatorIntegralAwayMulLocalEmbedding
import Development.AutomorphicArithmetic.LocalTestFunctions.CompProjFixedLevelEqOfLocalInvariance
import Development.AutomorphicArithmetic.LocalTestFunctions.ExistsTestFunctionIntegralProdLocalFactors

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem ft_comp (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    (AdelicGLn.finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) = finAt v (finEmb K n g) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.finiteRestrictedEquiv_apply, finAt_apply]
  have h := congrArg (fun z => (z.2 : AdelicGLn.FiniteAdelicGL K n) a b v) (prodEquiv_finEmb (K := K) (n := n) g)
  exact h.symm

private theorem ft_int (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.FiniteAdelicGL K n) (hg : g ∈ AdelicGLn.integralFiniteGL K n) (v : Pl K) :
    finAt v (finEmb K n g) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  rw [← ft_comp]
  exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hg v

private theorem ft_mul (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) (a b : AdelicGLn.FiniteAdelicGL K n) :
    finAt v (finEmb K n (a * b)) = finAt v (finEmb K n a) * finAt v (finEmb K n b) := by
  rw [map_mul, finAt_mul]

private theorem ft_list {M : Type*} [Monoid M] (x : M) : ∀ l : List M, (∀ a ∈ l, Commute a x ∨ a * x = a) → (∃ a ∈ l, a * x = a) →
    l.prod * x = l.prod := by
  intro l
  induction l with
  | nil => rintro - ⟨a, ha, -⟩; simp at ha
  | cons a t ih =>
    intro h1 h2
    by_cases ht : ∃ b ∈ t, b * x = b
    · rw [List.prod_cons, mul_assoc, ih (fun b hb => h1 b (List.mem_cons_of_mem _ hb)) ht]
    · have ha : a * x = a := by
        obtain ⟨b, hb, hbx⟩ := h2
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hbx
        · exact absurd ⟨b, hb, hbx⟩ ht
      have hc : Commute t.prod x := by
        refine Commute.list_prod_left _ _ fun b hb => ?_
        rcases h1 b (List.mem_cons_of_mem _ hb) with h | h
        · exact h
        · exact absurd ⟨b, hb, h⟩ ht
      rw [List.prod_cons, mul_assoc, hc.eq, ← mul_assoc, ha]

private theorem ft_ind {X : Type*} (S : Set X) {a b : X} (h : a ∈ S ↔ b ∈ S) :
    S.indicator (1 : X → ℂ) a = S.indicator (1 : X → ℂ) b := by
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h.2 hb)]; rfl
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun ha => hb (h.1 ha))]

private theorem operator_factorization_identity {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    (X G E0 Pu Pus A : E →L[ℂ] E) (c u k : ℂ) (hc : c ≠ 0) (hG : G = c • X) (h1 : G = A ∘L E0) (hE0 : E0 = u • Pu)
    (hP : A ∘L Pu = A ∘L Pus) (hu : u = c * k) : X = k • (A ∘L Pus) := by
  have h : c • X = c • (k • (A ∘L Pus)) := by
    rw [← hG, h1, hE0, ContinuousLinearMap.comp_smul, hP, hu, mul_smul]
  exact smul_right_injective _ hc h

private theorem ft_cc {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] (V : Subgroup X) (ho : IsOpen (V : Set X))
    (hc : IsCompact (V : Set X)) : ∃ κ : CompactlySupportedContinuousMap X ℂ, ∀ x, κ x = (V : Set X).indicator 1 x := by
  have hcl : IsClopen (V : Set X) := ⟨V.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨⟨(V : Set X).indicator 1, hcl.continuous_indicator continuous_const⟩,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, fun _ => rfl⟩

private theorem ft_intInd {X : Type*} [MeasurableSpace X] (m : Measure X) (S : Set X) (hS : MeasurableSet S) :
    ∫ x, S.indicator (1 : X → ℂ) x ∂m = ((m.real S : ℝ) : ℂ) := by
  show ∫ x, S.indicator (fun _ => (1 : ℂ)) x ∂m = _
  rw [integral_indicator_const (μ := m) (1 : ℂ) hS]
  simp

theorem UpperTheory.ConvolutionTheory.Tf.finTens :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (r : ℕ) (w : Fin r → Pl K), Function.Injective w →
      ∀ (f : ∀ v : Pl K, Gw n v → ℂ), (∀ i, Test (f (w i))) →
      (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) →
      ∃ e : TF K n, (∀ h, e h = ∏ᶠ v, f v (finAt v (finEmb K n h))) ∧
        (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ u ∈ U, ∀ h, e (u * h) = e h ∧ e (h * u) = e h) ∧
        ∀ [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))] (mw : ∀ i, Measure (Gw n (w i))),
          (∀ i, (mw i).IsHaarMeasure) → (∀ i, mw i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
          ∀ T : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (w i) (mw i) (f (w i)) (T i)) →
          ∀ US : Subgroup (AdelicGLn.FiniteAdelicGL K n), (∀ h, h ∈ US ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1) →
            Ofin μ m e = ((m.real (AdelicGLn.integralFiniteGL K n) : ℝ) : ℂ) • ((List.ofFn T).prod ∘L prj (fixF μ US)) := by
  intro K _ _ n μ _ m _ r w hw f hf hoff
  classical
  choose J hJco hJle hJinv using fun i => UpperTheory.exists_compactOpen_biinvariant_of_test K n (w i) (f (w i)) (hf i)
  obtain ⟨U, hUm, hUo, hUc⟩ := UpperTheory.exists_open_compact_level_subgroup K n r w J hJco
  let R : AdelicGLn.FiniteAdelicGL K n → ℂ :=
    ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1
  have hfree : ∀ i y x, R (AdelicGLn.localEmbedding (w i) y * x) = R x := fun i y x => UpperTheory.indicator_integral_away_mul_localEmbedding K n r w i y x
  let ψ : ∀ i, CompactlySupportedContinuousMap (Gw n (w i)) ℂ := fun i => ⟨⟨f (w i), (hf i).1.continuous⟩, (hf i).2⟩
  have hψ : ∀ i, ∀ k ∈ J i, ∀ x, ψ i (x * k) = ψ i x := fun i k hk x => (hJinv i k hk x).2
  obtain ⟨e', he', hOe'⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m U hUo hUc
  have hUpos : (m.real (U : Set (AdelicGLn.FiniteAdelicGL K n))) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_ne_top⟩
  have hUposC : ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hUpos
  let e₀ : TF K n := ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) • e'
  have he₀U : ∀ x, e₀ x = (U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) x := fun x => by
    show ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) • e' x = _
    rw [he']
    by_cases hx : x ∈ (U : Set (AdelicGLn.FiniteAdelicGL K n))
    · simp only [Set.indicator_of_mem hx, smul_eq_mul, Pi.one_apply]
      exact mul_inv_cancel₀ hUposC
    · simp only [Set.indicator_of_notMem hx, smul_zero]
  have he₀ : ∀ x, e₀ x = R x * ∏ i, (J i : Set (Gw n (w i))).indicator 1 (finAt (w i) (finEmb K n x)) := fun x => by
    rw [he₀U]
    exact UpperTheory.indicator_level_eq_prod_local_indicator K n r w J hJle U hUm x
  have hex : ∃ e : TF K n, ∀ x, e x = R x * ∏ i, f (w i) (finAt (w i) (finEmb K n x)) := by
    letI : ∀ i, MeasurableSpace (Gw n (w i)) := fun _ => borel _
    haveI : ∀ i, BorelSpace (Gw n (w i)) := fun _ => ⟨rfl⟩
    let mw : ∀ i, Measure (Gw n (w i)) := fun i => Measure.haar
    haveI : ∀ i, (mw i).IsHaarMeasure := fun i => inferInstanceAs (Measure.haar : Measure (Gw n (w i))).IsHaarMeasure
    obtain ⟨g, hg, -, -⟩ := UpperTheory.exists_testFunction_integral_prod_local_factors K n m r w hw mw J hJco ψ hψ R hfree e₀ he₀
    have hne : (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      have : (mw i).real (J i : Set (Gw n (w i))) ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨((hJco i).2.measure_pos (mw i) ⟨1, (J i).one_mem⟩).ne', (hJco i).1.measure_ne_top⟩
      exact_mod_cast this
    refine ⟨(∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ))⁻¹ • g, fun x => ?_⟩
    show (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ))⁻¹ • g x = _
    rw [hg, smul_eq_mul, inv_mul_cancel_left₀ hne]
    rfl
  obtain ⟨e, he⟩ := hex
  have hRl : ∀ u h, u ∈ AdelicGLn.integralFiniteGL K n → R (u * h) = R h := fun u h hu => by
    have hiff : (u * h ∈ {y : AdelicGLn.FiniteAdelicGL K n | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n}) ↔
        h ∈ {y : AdelicGLn.FiniteAdelicGL K n | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
      simp only [Set.mem_setOf_eq, ft_mul]
      exact forall_congr' fun v => imp_congr_right fun _ => Subgroup.mul_mem_cancel_left _ (ft_int K n u hu v)
    exact ft_ind _ hiff
  have hRr : ∀ u h, u ∈ AdelicGLn.integralFiniteGL K n → R (h * u) = R h := fun u h hu => by
    have hiff : (h * u ∈ {y : AdelicGLn.FiniteAdelicGL K n | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n}) ↔
        h ∈ {y : AdelicGLn.FiniteAdelicGL K n | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
      simp only [Set.mem_setOf_eq, ft_mul]
      exact forall_congr' fun v => imp_congr_right fun _ => Subgroup.mul_mem_cancel_right _ (ft_int K n u hu v)
    exact ft_ind _ hiff
  refine ⟨e, fun h => ?_, ⟨U, hUo, fun u hu h => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [he]
    exact (UpperTheory.finprod_local_eq_indicator_mul_prod K n r w hw f hoff h).symm
  · rw [he, he]
    have hk := (hUm u).1 hu
    congr 1
    · refine hRl u h hk.1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [ft_mul]
      exact (hJinv i _ (hk.2 i) _).1
  · rw [he, he]
    have hk := (hUm u).1 hu
    congr 1
    · refine hRr u h hk.1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [ft_mul]
      exact (hJinv i _ (hk.2 i) _).2
  · intro _ _ mw hmw hmK T hT US hUS
    haveI := hmw
    have hvne : ∀ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ) ≠ 0 := fun i => by
      have : (mw i).real (J i : Set (Gw n (w i))) ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨((hJco i).2.measure_pos (mw i) ⟨1, (J i).one_mem⟩).ne', (hJco i).1.measure_ne_top⟩
      exact_mod_cast this
    have hc : (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hvne i

    obtain ⟨g, hg, -, hgop⟩ := UpperTheory.exists_testFunction_integral_prod_local_factors K n m r w hw mw J hJco ψ hψ R hfree e₀ he₀
    have hT' : (fun i => (((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
        (AdelicGLn.localEmbedding (w i)) (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).1).integrated (mw i) (UnitaryRep.ccToL1 (mw i) (ψ i))) = T :=
      funext fun i => UpperTheory.integrated_rightRegular_eq_localOperator K n μ (w i) (mw i) (ψ i) (T i) (hT i)
    have h1 : Ofin μ m g = (List.ofFn T).prod ∘L Ofin μ m e₀ := by
      have := hgop (LL μ) ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj)
      rw [hT'] at this
      exact this
    let ν : Measure (archGroup K n) := Measure.haar
    have hsm := fun (c : ℂ) (e : TF K n) => ((UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.1 c 0 e).2
    have hge : g = (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) • e := by
      ext x
      show g x = (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) • e x
      rw [hg, he, smul_eq_mul]
      rfl
    have he₀op : Ofin μ m e₀ = ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) • prj (fixF μ U) := by
      rw [← hOe']
      exact hsm _ _

    have hA : ∀ i, ∀ k ∈ J i, (List.ofFn T).prod ∘L rhoL μ (w i) k = (List.ofFn T).prod := by
      intro i k hk
      refine ft_list (rhoL μ (w i) k) (List.ofFn T) ?_ ⟨T i, (List.mem_ofFn' _ _).2 ⟨i, rfl⟩, UpperTheory.localOperator_comp_rhoL_eq_of_right_invariant K n μ (w i) (mw i) (J i) (hJco i) (f (w i)) (fun k hk x => (hJinv i k hk x).2) (T i) (hT i) k hk⟩
      intro a ha
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
      by_cases hij : j = i
      · subst hij
        exact Or.inr (UpperTheory.localOperator_comp_rhoL_eq_of_right_invariant K n μ (w j) (mw j) (J j) (hJco j) (f (w j)) (fun k hk x => (hJinv j k hk x).2) (T j) (hT j) k hk)
      · exact Or.inl (UpperTheory.localOperator_commute_rhoF_of_trivial_at_place K n μ (w j) (mw j) (f (w j)) (T j) (hT j) _ ((UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 (w j) (fun h => hij (hw h)) k))
    have hP := UpperTheory.comp_proj_fixed_level_eq_of_local_invariance K n μ m r w hw J U US hUo hUc hUm hUS (List.ofFn T).prod hA

    have hvol : ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) =
        (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) * ((m.real (AdelicGLn.integralFiniteGL K n) : ℝ) : ℂ) := by
      choose κ hκv using fun i => ft_cc (GLnLocal.integralGL ((w i).adicCompletion K) n)
        (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)
      have hκ : ∀ i, ∀ k ∈ J i, ∀ x, κ i (x * k) = κ i x := fun i k hk x => by
        rw [hκv, hκv]
        exact ft_ind _ (Subgroup.mul_mem_cancel_right _ (hJle i hk))
      obtain ⟨gK, hgK, hint, -⟩ := UpperTheory.exists_testFunction_integral_prod_local_factors K n m r w hw mw J hJco κ hκ R hfree e₀ he₀
      have hgKv : ∀ x, gK x = (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) *
          (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) x := fun x => by
        rw [hgK, UpperTheory.indicator_level_eq_prod_local_indicator K n r w (fun i => GLnLocal.integralGL ((w i).adicCompletion K) n) (fun _ => le_rfl)
          (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))
          (fun h => ⟨fun hh => ⟨hh, fun i => ft_int K n h hh (w i)⟩, And.left⟩) x]
        simp only [hκv]
        rfl
      have hKm : MeasurableSet (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) :=
        (AdelicGLn.isOpen_integralFiniteGL K n).measurableSet
      have i1 : ∫ x, gK x ∂m = (∏ i, (((mw i).real (J i : Set (Gw n (w i))) : ℝ) : ℂ)) * ((m.real (AdelicGLn.integralFiniteGL K n) : ℝ) : ℂ) := by
        simp only [hgKv]
        rw [integral_const_mul, ft_intInd m _ hKm]
      have i2 : ∀ i, ∫ y, κ i y ∂(mw i) = 1 := fun i => by
        simp only [hκv]
        rw [ft_intInd (mw i) _ (GLnLocal.isOpen_integralGL _ n).measurableSet, Measure.real, hmK i]
        simp
      have i3 : ∫ x, e₀ x ∂m = ((m.real (U : Set (AdelicGLn.FiniteAdelicGL K n)) : ℝ) : ℂ) := by
        simp only [he₀U]
        exact ft_intInd m _ hUo.measurableSet
      rw [← i1, hint, i3]
      simp only [i2, Finset.prod_const_one, one_mul]
    exact operator_factorization_identity (Ofin μ m e) (Ofin μ m g) (Ofin μ m e₀) (prj (fixF μ U)) (prj (fixF μ US)) (List.ofFn T).prod _ _ _ hc
      (by rw [hge]; exact hsm _ e) h1 he₀op hP hvol
