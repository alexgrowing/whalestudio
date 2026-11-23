import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import GroundTheory.AutomorphicForms.ReductionDirichlet
import GroundTheory.AutomorphicForms.ReductionIdele
open UpperTheory.V.Sd.Eis
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V

private theorem idele_split (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom x) * finId F (Units.map (pFin F).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h3, h4]

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) :
    Continuous fun x : Ad F => TR.pInf F x v :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
    ((continuous_apply v).comp continuous_fst)

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ray_class_group_finite :
    UpperTheory.V.Sd.Eis.RayFin := by
  intro F _ _ _ H hK hR hf
  have hopen : IsOpen (H : Set (Ideles F)) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    have c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ) :=
      Continuous.units_map _ continuous_snd
    have h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H := by
      have := c1.continuousAt (x := 1)
      rw [ContinuousAt, map_one] at this
      exact this hf
    have h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v := by
      rw [Filter.eventually_all]
      intro v
      have c : Continuous fun x : Ideles F => TR.pInf F x.val v := (cont_pInf F v).comp Units.continuous_val
      refine c.continuousAt.eventually (lt_mem_nhds ?_)
      simp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← idele_split F x]
    exact H.mul_mem (hR _ hx2) hx1
  refine ⟨hopen, ?_⟩
  have hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H := by
    intro ρ hρ
    set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz
    have e : Units.map (pFin F).toMonoidHom z = 1 := by
      refine Units.ext ?_
      ext v
      exact congrArg _ (posIdele_finite ρ hρ v)
    have e2 := idele_split F z
    rw [e, map_one, mul_one] at e2
    rw [← e2, ← map_pow]
    refine hR _ fun v => ?_
    set y := Units.map (TR.pInf F).toMonoidHom z
    have hy : y.val v ≠ 0 := by
      have := congrFun y.mul_inv v
      exact left_ne_zero_of_mul_eq_one this
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    positivity
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  have hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H := by
    intro t
    have hn : 2 * Module.finrank ℚ F ≠ 0 := mul_ne_zero two_ne_zero Module.finrank_pos.ne'
    have ht : 0 < (ideleModule F t : ℝ) := (ideleModule F t).2
    set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef
    have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
    have hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
    have hzH := hsq ρ hρ
    have hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t := by
      refine Subtype.ext ?_
      rw [sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]
      rfl
    generalize (posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt
    have h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1 := by
      rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
    obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
    refine ⟨_, hcS, ?_⟩
    have e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹ := by
      rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    rw [e]
    exact H.mul_mem hzH (H.inv_mem (hK c))
  haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen
  have hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  haveI : Finite (Ideles F ⧸ H) := by
    refine Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, hst⟩ := hcov t
    exact ⟨s, hs, QuotientGroup.eq.2 hst⟩
  exact Subgroup.finiteIndex_of_finite_quotient
