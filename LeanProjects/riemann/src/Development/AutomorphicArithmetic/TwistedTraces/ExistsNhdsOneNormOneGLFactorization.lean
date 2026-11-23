import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_one_normOneGL_factorization :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (N : Set (archGroup K n)) (U : Subgroup (AdelicGLn.integralFiniteGL K n)), N ∈ 𝓝 (1 : archGroup K n) → IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → ∃ N' ∈ 𝓝 (1 : normOneGL K n), ∀ g ∈ N', ∃ a ∈ N, ∃ u ∈ U, g = archP K n a * retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n)) := by
  intro K _ _ n N U hN hU
  have hU' : IsOpen (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have hp : Continuous fun g : normOneGL K n => AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun g : normOneGL K n =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1 :=
    (archEquiv K n).continuous.comp hp.fst
  have hf : Continuous fun g : normOneGL K n =>
      (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := hp.snd
  refine ⟨(fun g : normOneGL K n =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1) ⁻¹' N ∩
    (fun g : normOneGL K n => (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2) ⁻¹'
      (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))), Filter.inter_mem ?_ ?_, ?_⟩
  · refine ha.continuousAt.preimage_mem_nhds ?_
    simpa only [OneMemClass.coe_one, map_one, Prod.fst_one] using hN
  · refine (hU'.preimage hf).mem_nhds ⟨1, U.one_mem, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
  · rintro g ⟨hg, u, hu, e⟩
    refine ⟨_, hg, u, hu, ?_⟩
    have e' : (u : AdelicGLn.FiniteAdelicGL K n) = (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := e
    rw [e']
    calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
      _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
            finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
      _ = _ := by rw [retractOne_mul, retract_infEmb]
