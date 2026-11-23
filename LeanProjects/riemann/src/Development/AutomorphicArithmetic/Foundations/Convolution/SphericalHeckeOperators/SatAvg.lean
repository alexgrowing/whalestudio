import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.Mac
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.HlEval
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ThPMul

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

section Aux3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F))

private theorem theta_sum₂ {ι : Type*} (S : Finset ι) (c : ι → ℂ) (y : ι → LaurentRing n) :
    thP μ (∑ i ∈ S, c i • y i) = ∑ i ∈ S, c i • thP μ (y i) := by
  have h : ∀ r : LaurentRing n, thP μ r = Finsupp.linearCombination ℂ (th μ) r.coeff := fun r => rfl
  simp only [h, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul, map_sum, map_smul]

variable [BorelSpace (GL (Fin n) F)] [μ.IsHaarMeasure]

private theorem oneK_eq (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) :
    oneK F n = (HeckeAlgebra.idem μ (isCompact_integralGL F n) (isOpen_integralGL F n) : HeckeAlgebra μ) := by
  funext x
  rw [HeckeAlgebra.idem_apply, Measure.real, hK]
  simp [oneK, Set.indicator]

private theorem oneK_mul (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) :
    groupConv μ (oneK F n) (oneK F n) = oneK F n := by
  rw [oneK_eq μ hK]
  exact congrArg (fun x : HeckeAlgebra μ => (x : GL (Fin n) F → ℂ))
    (HeckeAlgebra.isIdempotentElem_idem (μ := μ) (isCompact_integralGL F n) (isOpen_integralGL F n)).eq

end Aux3

private theorem int_sandwich {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) {φ : GL (Fin n) F → ℂ}
    (hφ : φ ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (z : Fin n → ℂˣ) :
    ∫ x, groupConv μ (oneK F n) (groupConv μ φ (oneK F n)) x * sphericalFun (paramChar F z) x ∂μ =
      ∫ g, φ g * zonalSpherical μ z g ∂μ := by
  have hχ := isUnramified_paramChar (F := F) z
  have hs := Parabolic.isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n))
    (charRep (paramChar F z))
  let ev : Module.Dual ℂ (principalSeriesSpace F n (paramChar F z)) :=
    (LinearMap.proj 1).comp (principalSeriesSpace F n (paramChar F z)).subtype
  have hev : ∀ g, ev (principalSeries F n (paramChar F z) g (sphericalVector hχ)) = sphericalFun (paramChar F z) g :=
    fun g => by
      change ((principalSeries F n (paramChar F z) g (sphericalVector hχ) :
        principalSeriesSpace F n (paramChar F z)) : GL (Fin n) F → ℂ) 1 = _
      rw [coe_indRep_apply, one_mul]
      rfl
  have h1 := dual_heckeAct μ (groupConv_mem μ (oneK_mem (F := F) (n := n)) (groupConv_mem μ hφ oneK_mem))
    (hs (sphericalVector hχ)) ev
  have hKv : heckeAct μ (principalSeries F n (paramChar F z)) (oneK F n) (sphericalVector hχ) = sphericalVector hχ := by
    rw [oneK_eq μ hK]
    exact HeckeAlgebra.heckeAct_idem_of_mem _ _ (sphericalVector_mem_fixedVectors hχ)
  have h2 := dual_heckeAct μ hφ (hs (sphericalVector hχ))
    (ev.comp (HeckeAlgebra.heckeRep (μ := μ) hs (HeckeAlgebra.mk μ _ (oneK_mem (F := F) (n := n)))))
  rw [heckeAct_groupConv oneK_mem (groupConv_mem μ hφ oneK_mem) (hs _), heckeAct_groupConv hφ oneK_mem (hs _)] at h1
  erw [hKv] at h1
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (h1.symm.trans (h2.trans
    (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))))
  · exact congrArg _ (hev x).symm
  · refine congrArg (φ g * ·) ?_
    refine (dual_heckeAct μ (oneK_mem (F := F) (n := n)) (hs _) ev).trans ?_
    rw [zonalSpherical, Measure.real, hK, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine congrArg (oneK F n x * ·) ?_
    rw [← hev, map_mul]
    rfl

theorem UpperTheory.ConvolutionTheory.H.satAvg :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], μ (integralGL F n : Set (GL (Fin n) F)) = 1 →
      ∀ r : LaurentRing n, Dom (r * dPol n 1) →
      ∀ h : SphericalHecke μ (F := F) (n := n), satakeTransform μ h = symSum (r * dPol n ((qF F : ℂ))⁻¹) →
        vPoly n ((qF F : ℂ))⁻¹ • groupConv μ (oneK F n) (groupConv μ (thP μ (r * dPol n 1)) (oneK F n)) = fun x => (h : HeckeAlgebra μ) x := by
  intro F _ _ _ _ n _ _ μ _ hK r hr h hh
  set t : ℂ := ((qF F : ℂ))⁻¹ with ht
  have hφ := (thPMul F n μ _ _ hr hr).2.1
  have hm := groupConv_mem μ (oneK_mem (F := F) (n := n)) (groupConv_mem μ hφ oneK_mem)
  have hKl : ∀ k ∈ integralGL F n, ∀ x, oneK F n (k * x) = oneK F n x ∧ oneK F n (x * k) = oneK F n x := by
    rw [oneK_eq μ hK]
    exact HeckeAlgebra.idem_mem_biInvariant _ _
  let H : SphericalHecke μ (F := F) (n := n) :=
    HeckeAlgebra.HeckeAlgebraLevel.mk _ _ (HeckeAlgebra.mk μ _ (Submodule.smul_mem _ (vPoly n t) hm)) fun k hk x => by
      simp only [HeckeAlgebra.coe_mk, Pi.smul_apply]
      rw [cv_mul_left μ fun g => (hKl k hk g).1,
        groupConv_mul_right fun g => groupConv_mul_right (fun g => (hKl k hk g).2) g]
      exact ⟨rfl, rfl⟩
  suffices hH : H = h by
    rw [← hH]
    rfl
  apply satakeTransform_injective
  rw [hh, ← sub_eq_zero]
  refine (mul_eq_zero.1 (eq_zero_of_forall_evalAt fun z => ?_)).resolve_right (dPol_ne_zero n 1)
  rw [map_mul]
  by_cases hz : evalAt z (dPol n 1) = 0
  · rw [hz, mul_zero]
  refine mul_eq_zero_of_left ?_ _
  have hinj := inj_of_dPol hz
  have h1 := integral_mul_sphericalFun z H 1
  rw [sphericalFun_one (isUnramified_paramChar z), mul_one] at h1
  have hΓ : Continuous (zonalSpherical μ z) :=
    continuous_of_mul_right_invariant fun g k hk => zonalSpherical_mul_right z g hk
  have hth : ∀ a : Fin n → ℤ, Antitone a → th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
    fun a ha => by
      have := thPMul F n μ _ _ (dom_monomial ha) (dom_monomial ha)
      rw [thP_monomial] at this
      exact this.2.1
  have h2 : evalAt z (satakeTransform μ H) = vPoly n t * ∫ g, thP μ (r * dPol n 1) g * zonalSpherical μ z g ∂μ := by
    rw [← h1, ← int_sandwich μ hK hφ z, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [one_mul, ← mul_assoc]
    rfl
  have h3 : vPoly n t * ∫ g, thP μ (r * dPol n 1) g * zonalSpherical μ z g ∂μ =
      ∑ a ∈ (r * dPol n 1).coeff.support, (r * dPol n 1).coeff a * evalAt z (hlR t a) := by
    simp only [thP, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun a ha => (integrable_mul_of_mem (hth a (hr a ha)) hΓ).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [integral_const_mul, ← mac F n μ z a (hr a ha), mul_left_comm]
  rw [map_sub, h2, h3, sub_eq_zero, symSum, map_sum]
  simp only [(hlEval n t z hinj _).2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h4 := evalAt_apply (z ∘ σ) (r * dPol n 1)
  have h5 := (hlEval n t z hinj 0).1 σ
  simp only [mul_left_comm ((r * dPol n 1).coeff _)]
  rw [← Finset.mul_sum, evalAt_permAct]
  rw [Finsupp.sum] at h4
  rw [← h4, map_mul, map_mul]
  field_simp
