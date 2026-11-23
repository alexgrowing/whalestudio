import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

theorem UpperTheory.levF_isOpen_isCompact_le_integral :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (lev : ∀ v : Pl K, Subgroup (GL (Fin n) (v.adicCompletion K))) (S : Finset (Pl K)),
      (∀ v ∈ S, IsOpen (lev v : Set (GL (Fin n) (v.adicCompletion K))) ∧ lev v ≤ GLnLocal.integralGL (v.adicCompletion K) n) →
      (∀ v, v ∉ S → lev v = GLnLocal.integralGL (v.adicCompletion K) n) →
      IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
        levF lev ≤ AdelicGLn.integralFiniteGL K n ∧
        ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), J ≤ lev w → J.map (AdelicGLn.localEmbedding w) ≤ levF lev := by
  classical
  intro K _ _ n lev S hS hS'
  have hmem : ∀ h : AdelicGLn.FiniteAdelicGL K n,
      h ∈ levF lev ↔ ∀ v, AdelicGLn.finiteRestrictedEquiv K n h v ∈ lev v := fun h => Iff.rfl
  have hint : levF lev ≤ AdelicGLn.integralFiniteGL K n := by
    intro h hh
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro v
    have hv := (hmem h).1 hh v
    by_cases hvS : v ∈ S
    · exact (hS v hvS).2 hv
    · rwa [hS' v hvS] at hv
  have hev : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n =>
      (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K)) := fun v =>
    (_root_.RestrictedProduct.continuous_eval v).comp (AdelicGLn.finiteRestrictedEquiv K n).continuous
  have hVo : IsOpen ((AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
      ⋂ v ∈ S, (fun h : AdelicGLn.FiniteAdelicGL K n =>
        (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K))) ⁻¹'
          (lev v : Set (GL (Fin n) (v.adicCompletion K)))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (isOpen_biInter_finset fun v hv => (hS v hv).1.preimage (hev v))
  have hopen : IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levF lev) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨one_mem _, ?_⟩
      simp only [Set.mem_iInter]
      intro v _
      exact (levF lev).one_mem v
    · rintro h ⟨h1, h2⟩
      simp only [Set.mem_iInter] at h2
      refine (hmem h).2 fun v => ?_
      by_cases hvS : v ∈ S
      · exact h2 v hvS
      · rw [hS' v hvS]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1 v
  refine ⟨hopen, ?_, hint, ?_⟩
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w J hJ _ ⟨x, hx, rfl⟩
    obtain ⟨-, h1, h2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hJ hx
    · rw [h2 v hv]
      exact one_mem _
