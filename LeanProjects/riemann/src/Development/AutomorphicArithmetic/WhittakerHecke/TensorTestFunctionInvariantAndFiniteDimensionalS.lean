import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem trEx {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : CompactlySupportedContinuousMap G ℂ) (a : G) :
    ∃ f' : CompactlySupportedContinuousMap G ℂ, ∀ g, f' g = f (a * g) :=
  ⟨⟨⟨fun g => f (a * g), f.continuous.comp (continuous_const.mul continuous_id)⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a)⟩, fun _ => rfl⟩

theorem UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
          U ≤ AdelicGLn.integralFiniteGL K n → IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → (∀ u ∈ U, ∀ h, e (u * h) = e h) →
          (∀ u ∈ U, ∀ z, tens β e ((MultiplicityOne.finProj K n u)⁻¹ * z) = tens β e z) ∧ (LeftFin β →
          FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
            fun z : normOneGL K n => tens β e ((Subgroup.inclusion maxCompact_le_normOneGL k)⁻¹ * z)))) := by
  intro K _ _ n hn β e U hU hUo he
  have happ : ∀ (β : TI K n) (e : TF K n) x, tens β e x = tensFun β e x :=
    fun β e => (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1
  refine ⟨fun u hu z => ?_, fun hβ => ?_⟩
  · have h1 : (MultiplicityOne.finProj K n u : AdelicGLn.AdelicGL K n) = finEmb K n u :=
      congrArg Subtype.val (MultiplicityOne.finProj_eq_finOne ⟨u, hU hu⟩)
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, map_mul, map_mul, map_inv, map_inv, infPart_finEmb,
      finPart_finEmb, inv_one, one_mul, he _ (U.inv_mem hu)]
  · choose tb htb using trEx β
    choose te hte using trEx e
    let Kf := AdelicGLn.integralFiniteGL K n
    let V : Subgroup Kf := U.subgroupOf Kf
    have hV : IsOpen (V : Set Kf) := hUo.preimage continuous_subtype_val
    haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
    haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
    let c : TI K n →ₗ[ℂ] (archGroup K n → ℂ) :=
      { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hc : Function.Injective c := DFunLike.coe_injective
    let T : Submodule ℂ (TI K n) := Submodule.span ℂ (Set.range fun k : archCompact K n => tb k)
    haveI : FiniteDimensional ℂ T := by
      unfold LeftFin at hβ
      have hle : T.map c ≤ Submodule.span ℂ (Set.range fun k : archCompact K n =>
          fun g : archGroup K n => β ((k : archGroup K n) * g)) :=
        (Submodule.map_span _ _).le.trans (Submodule.span_mono (by
          rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, funext fun g => (htb k g).symm⟩))
      have := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hc _).symm
    let L : TF K n → TI K n →ₗ[ℂ] (normOneGL K n → ℂ) := fun e' =>
      { toFun := fun f => tens f e'
        map_add' := fun f g => by rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn f e').2.2.1]; rfl
        map_smul' := fun a f => by rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn f e').2.2.2.2 a).1]; rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V, T.map (L (te (q.out.1)⁻¹)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    let kf : Kf := ⟨finPart K n k.1, finPart_mem_integralFiniteGL k.2⟩
    let ka : archCompact K n := ⟨infPart K n k.1, archPart_mem_archCompact k.2⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
    refine Submodule.mem_iSup_of_mem (QuotientGroup.mk kf) ⟨_, Submodule.subset_span ⟨ka⁻¹, rfl⟩, ?_⟩
    rw [hv]
    funext z
    change tens (tb (infPart K n k.1)⁻¹) (te (finPart K n k.1 * v.1.1)⁻¹) z = tens β e _
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, map_mul, map_mul, map_inv, map_inv, hte,
      mul_inv_rev, mul_assoc, he _ (U.inv_mem (show v.1.1 ∈ U from v.2))]
    congr 1
    simp only [kbar, htb, mul_assoc]
