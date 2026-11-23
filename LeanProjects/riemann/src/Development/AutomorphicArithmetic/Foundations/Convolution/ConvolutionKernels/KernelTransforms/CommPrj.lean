import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem commute_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ (∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0) ∧ Commute T (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  have a1 : ∀ v, prj V v ∈ V := fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v)
  have a3 : ∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0 := fun v w hw =>
    Submodule.starProjection_inner_eq_zero v w ((hm _).2 hw)
  refine ⟨a1, fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), a3, ?_⟩
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 (h1 _ (a1 v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact a3 v _ (h2 w ((hm _).1 hw))

theorem UpperTheory.ConvolutionTheory.Tf.commPrj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
      IsClosed (fixF μ U : Set (LL μ)) ∧ (∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v) ∧ (∀ v, prj (fixF μ U) v ∈ fixF μ U) ∧
      (∀ v ∈ fixF μ U, prj (fixF μ U) v = v) ∧ (∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) ∧ prj (fixF μ U) ∘L rhoF μ u = prj (fixF μ U)) ∧
      (∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h') ∧ rhoF μ 1 = 1 ∧ (∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹) ∧
      ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
  intro K _ _ n μ _ U
  have hmem : ∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := fun v => by
    simp only [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  have hcl : IsClosed (fixF μ U : Set (LL μ)) := by
    have : (fixF μ U : Set (LL μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := fun h h' => by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [rhoF, map_mul, UnitaryRep.map_mul_apply, ContinuousLinearMap.comp_apply]
  have hone : rhoF μ 1 = 1 := by
    simp only [rhoF, map_one, UnitaryRep.map_one]
  have hadj : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := fun h => by
    unfold rhoF
    rw [UnitaryRep.adjoint_map, map_inv (MultiplicityOne.finProj K n)]
  have hpres : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → ∀ v ∈ fixF μ U, T v ∈ fixF μ U := by
    intro T hT v hv
    rw [hmem] at hv ⊢
    intro u hu
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hT u hu).eq
    simp only [ContinuousLinearMap.mul_apply, hv u hu] at this
    exact this.symm
  have hT : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
    intro T hT
    refine (commute_prj _ hcl T (hpres T hT) (hpres _ fun u hu => ?_)).2.2.2
    have := (hT u⁻¹ (U.inv_mem hu)).star_star
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hadj, inv_inv] at this
  obtain ⟨a1, a2, -, -⟩ := commute_prj _ hcl 0 (fun v _ => by simp) (fun v _ => by simp)
  have hl : ∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) := fun u hu =>
    ContinuousLinearMap.ext fun v => (hmem _).1 (a1 v) u hu
  refine ⟨hcl, hmem, a1, a2, fun u hu => ⟨hl u hu, ?_⟩, hmul, hone, hadj, hT⟩
  have hfix : ∀ u ∈ U, ∀ v ∈ fixF μ U, rhoF μ u v ∈ fixF μ U := fun u hu v hv => by
    rw [(hmem v).1 hv u hu]; exact hv
  have hc := (commute_prj _ hcl (rhoF μ u) (hfix u hu) (by rw [hadj]; exact hfix _ (U.inv_mem hu))).2.2.2
  exact hc.eq.symm.trans (hl u hu)
