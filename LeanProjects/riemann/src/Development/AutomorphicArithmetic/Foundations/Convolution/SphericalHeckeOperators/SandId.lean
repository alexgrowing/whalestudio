import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SandPS
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ConstTerm
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SetIntegralCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ThPMul
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.IntegralConv
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.GapDom

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section SlopeTestRemainingChoices

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem cv_assoc {a b c : G → ℂ} (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : b ∈ locallyConstantCompactSupport G ℂ ℂ) (hc : c ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (groupConv μ a b) c = groupConv μ a (groupConv μ b c) :=
  congrArg (fun x : HeckeAlgebra μ => (x : G → ℂ))
    (mul_assoc (HeckeAlgebra.mk μ a ha) (HeckeAlgebra.mk μ b hb) (HeckeAlgebra.mk μ c hc))

private theorem cv_smul_left (c : ℂ) (a b : G → ℂ) : groupConv μ (c • a) b = c • groupConv μ a b := by
  funext x
  simp only [groupConv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem cv_smul_right (c : ℂ) (a b : G → ℂ) : groupConv μ a (c • b) = c • groupConv μ a b := by
  funext x
  simp only [groupConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

private theorem cv_sub_right {a b c : G → ℂ} (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : b ∈ locallyConstantCompactSupport G ℂ ℂ) (hc : c ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ a (b - c) = groupConv μ a b - groupConv μ a c :=
  congrArg (fun x : HeckeAlgebra μ => (x : G → ℂ))
    (mul_sub (HeckeAlgebra.mk μ a ha) (HeckeAlgebra.mk μ b hb) (HeckeAlgebra.mk μ c hc))

private theorem cv_sum_right {ι : Type*} (S : Finset ι) {a : G → ℂ} {b : ι → G → ℂ}
    (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : ∀ i ∈ S, b i ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ a (∑ i ∈ S, b i) = ∑ i ∈ S, groupConv μ a (b i) := by
  funext x
  simp only [groupConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => integrable_mul_of_mem ha
    ((hb i hi).1.continuous.comp (continuous_inv.mul continuous_const))

private theorem cv_sum_left {ι : Type*} (S : Finset ι) {a : G → ℂ} {b : ι → G → ℂ}
    (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : ∀ i ∈ S, b i ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (∑ i ∈ S, b i) a = ∑ i ∈ S, groupConv μ (b i) a := by
  funext x
  simp only [groupConv, Finset.sum_apply, Finset.sum_mul]
  exact integral_finsetSum _ fun i hi => integrable_mul_of_mem (hb i hi)
    (ha.1.continuous.comp (continuous_inv.mul continuous_const))

private theorem cv_mul_left {a b : G → ℂ} {k : G} (hk : ∀ g, a (k * g) = a g) (x : G) :
    groupConv μ a b (k * x) = groupConv μ a b x := by
  unfold groupConv
  rw [← integral_mul_left_eq_self (fun y => a y * b (y⁻¹ * (k * x))) k]
  simp [hk, mul_assoc]

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem oneK_mem : oneK F n ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  indicator_mem_locallyConstantCompactSupport (isCompact_integralGL F n) (isOpen_integralGL F n) 1

variable [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F))

private theorem thP_monomial (a : Fin n → ℤ) : thP μ (monomial a) = th μ a := by
  unfold thP
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul]

private theorem dom_monomial {a : Fin n → ℤ} (ha : Antitone a) : Dom (monomial a) := by
  intro b hb
  rw [AddMonoidAlgebra.coeff_single] at hb
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
  exact ha

end Aux2

private theorem dPol_ne_zero (n : ℕ) (t : ℂ) : dPol n t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p hp h => ?_
  have hp' : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  have hne : (Pi.single p.2 1 : Fin n → ℤ) ≠ Pi.single p.1 1 := fun e => by
    have := congrFun e p.1
    simp [hp'.ne] at this
  have := congrArg (fun y : LaurentRing n => y.coeff (Pi.single p.1 1)) h
  simp [Finsupp.single_apply, hne] at this

private theorem inj_of_dPol {n : ℕ} {z : Fin n → ℂˣ} (h : evalAt z (dPol n 1) ≠ 0) : Function.Injective z := by
  have key : ∀ i j, i < j → z i ≠ z j := fun i j hij e => by
    refine h ?_
    unfold dPol
    rw [map_prod]
    refine Finset.prod_eq_zero (i := (i, j)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩) ?_
    have hv : ∀ a, evalAt z (varL a) = z a := fun a => by
      rw [evalAt_single, one_mul, monomialChar_apply, Finset.prod_eq_single a] <;> simp +contextual [Pi.single_apply]
    simp [hv, e]
  intro i j e
  rcases lt_trichotomy i j with h | h | h
  · exact absurd e (key _ _ h)
  · exact h
  · exact absurd e.symm (key _ _ h)

theorem UpperTheory.ConvolutionTheory.H.sandId :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], μ (integralGL F n : Set (GL (Fin n) F)) = 1 →
      ∃ ν₁ ν₂ : Fin n → ℤ, Gap n ν₁ ∧ Gap n ν₂ ∧
        vPoly n ((qF F : ℂ))⁻¹ • sand μ ν₁ ν₂ = thP μ (monomial (ν₁ + ν₂) * dPol n ((qF F : ℂ))⁻¹) := by
  intro F _ _ _ _ n _ _ μ _ hK
  set t : ℂ := ((qF F : ℂ))⁻¹
  let ν : Fin n → ℤ := fun i => -((n : ℤ) * (i : ℕ))
  have hν : Gap n ν := fun i j hij => by
    have h1 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
    have h2 : (0 : ℤ) ≤ n := by positivity
    simp only [ν]
    nlinarith
  have hνa : Antitone ν := fun i j hij => by
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · have := hν i j hij
      omega
  have hg := gapDom n ν hν
  have hνν := hg.2.2 ν hνa
  have hth : ∀ a : Fin n → ℤ, Antitone a → th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (th μ a) :=
    fun a ha => by
      have := thPMul F n μ _ _ (dom_monomial ha) (dom_monomial ha)
      rw [thP_monomial] at this
      exact ⟨this.2.1, this.2.2.1⟩
  have hD := (gapDom n _ hνν).2.1 t
  have hP := thPMul F n μ _ _ hD hD
  have hterm : ∀ S ∈ (pairs n).powerset, groupConv μ (oneK F n) (th μ (ν + eR S)) ∈
      locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun S hS =>
    groupConv_mem μ oneK_mem (hth _ (hg.1 S hS).2).1
  have hterm' : ∀ S ∈ (pairs n).powerset,
      sgS S • groupConv μ (th μ (ν + eL S)) (groupConv μ (oneK F n) (th μ (ν + eR S))) ∈
      locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun S hS =>
    Submodule.smul_mem _ _ (groupConv_mem μ (hth _ (hg.1 S hS).1).1 (hterm S hS))
  have hs : sand μ ν ν ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := Submodule.sum_mem _ hterm'
  have hsI : BiI F (sand μ ν ν) := fun g y hy => by
    simp only [sand, Finset.sum_apply, Pi.smul_apply]
    constructor
    · exact Finset.sum_congr rfl fun S hS => by
        rw [cv_mul_left μ fun g => ((hth _ (hg.1 S hS).1).2 g y hy).1]
    · exact Finset.sum_congr rfl fun S hS => by
        rw [groupConv_mul_right fun g => groupConv_mul_right (fun g => ((hth _ (hg.1 S hS).2).2 g y hy).2) g]
  set T := vPoly n t • sand μ ν ν - thP μ (monomial (ν + ν) * dPol n t) with hT
  have hTm : T ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hs) hP.2.1
  have hTI : BiI F T := fun g y hy => by
    simp only [hT, Pi.sub_apply, Pi.smul_apply, (hsI g y hy).1, (hsI g y hy).2, (hP.2.2.1 g y hy).1,
      (hP.2.2.1 g y hy).2, and_self]
  have hD0 : (∏ σ : Equiv.Perm (Fin n), permAct σ (dPol n t)) * dPol n 1 ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun σ _ h => dPol_ne_zero n t ?_) (dPol_ne_zero n 1)
    have := congrArg (permAct σ⁻¹) h
    rwa [permAct_permAct, inv_mul_cancel, permAct_one, map_zero] at this
  have hct := constTerm F n μ T hTm hTI _ hD0 fun z hz f hf => by
    rw [map_mul, map_prod] at hz
    have h1 := sandPS F n μ hK ν ν hν hν z (inj_of_dPol (right_ne_zero_of_mul hz))
      (fun σ => by
        rw [← evalAt_permAct]
        exact Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hz) σ (Finset.mem_univ _)) f hf
    have hfc : Continuous f := by
      refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open f).2 fun g => ?_)
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (iwahori F n : Set (GL (Fin n) F)),
        (isOpen_iwahori F n).preimage (by fun_prop), by simp [one_mem], fun y hy => ?_⟩
      rw [← hf.2 g _ hy, mul_inv_cancel_left]
    simp only [hT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_assoc]
    rw [integral_sub ((integrable_mul_of_mem hs hfc).const_mul _) (integrable_mul_of_mem hP.2.1 hfc),
      integral_const_mul, h1, sub_self]
  obtain ⟨a, ha, ha0⟩ := jacq F n μ T hTm hTI hct
  refine ⟨a + ν, ν, hg.2.2 a ha, hν, ?_⟩
  have h0 : groupConv μ (th μ a) T = 0 := by
    rw [th, cv_smul_left, ha0, smul_zero]
  rw [hT, cv_sub_right μ (hth a ha).1 (Submodule.smul_mem _ _ hs) hP.2.1, sub_eq_zero, cv_smul_right] at h0
  have h1 := (thPMul F n μ _ _ (dom_monomial ha) hD).2.2.2
  rw [thP_monomial, ← mul_assoc, ← monomial_add, ← add_assoc] at h1
  rw [← h1, ← h0]
  congr 1
  unfold sand
  rw [cv_sum_right μ _ (hth a ha).1 hterm']
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [cv_smul_right, ← cv_assoc μ (hth a ha).1 (hth _ (hg.1 S hS).1).1 (hterm S hS),
    thMul F n μ _ _ ha (hg.1 S hS).1, add_assoc]
