import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SandId
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SatAvg
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ThPMul
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.GapDom
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.VandSum

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

theorem UpperTheory.ConvolutionTheory.H.core :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], μ (integralGL F n : Set (GL (Fin n) F)) = 1 →
      ∃ ν : Fin n → ℤ, ∀ r : LaurentRing n, Dom r → ∀ h : SphericalHecke μ (F := F) (n := n),
        satakeTransform μ h = symSum (monomial ν * dPol n ((qF F : ℂ))⁻¹ * r) →
        (thP μ (monomial ν * dPol n ((qF F : ℂ))⁻¹ * r) - fun x => (h : HeckeAlgebra μ) x) ∈ comm μ := by
  intro F _ _ _ _ n _ _ μ _ hK
  set t : ℂ := ((qF F : ℂ))⁻¹
  obtain ⟨ν₁, ν₂, h₁, h₂, hid⟩ := sandId F n μ hK
  refine ⟨ν₁ + ν₂, fun r hr h hh => ?_⟩
  have hν₁ : Antitone ν₁ := fun i j hij => by
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · have := h₁ i j hij
      omega
  have g₁ := gapDom n ν₁ h₁
  have g₂ := gapDom n ν₂ h₂
  have g₃ := gapDom n _ (g₂.2.2 ν₁ hν₁)
  have hth : ∀ a : Fin n → ℤ, Antitone a → th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
    fun a ha => by
      have := thPMul F n μ _ _ (dom_monomial ha) (dom_monomial ha)
      rw [thP_monomial] at this
      exact this.2.1
  have hr' := (thPMul F n μ _ _ hr hr).2.1
  have hv : ∑ S ∈ (pairs n).powerset, sgS S • monomial (eL S + eR S) = dPol n 1 :=
    eq_of_forall_evalAt fun z => by
      have := vandSum n z 1 1
      simp only [Equiv.Perm.coe_one, Function.comp_id, if_true] at this
      rw [← this, map_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [map_smul, evalAt_single, one_mul, monomialChar_add, smul_eq_mul]
  have hD1 : Dom (monomial (ν₁ + ν₂) * r * dPol n 1) := by
    rw [mul_right_comm]
    exact (thPMul F n μ _ _ (g₃.2.1 1) hr).1
  have hsat := satAvg F n μ hK (monomial (ν₁ + ν₂) * r) hD1 h (by rw [hh, mul_right_comm])
  let C : Finset (Fin n × Fin n) → LaurentRing n := fun S => monomial (ν₂ + eR S) * (r * monomial (ν₁ + eL S))
  have hA : ∀ S ∈ (pairs n).powerset, Dom (r * monomial (ν₁ + eL S)) := fun S hS =>
    (thPMul F n μ _ _ hr (dom_monomial (g₁.1 S hS).1)).1
  have hC : ∀ S ∈ (pairs n).powerset, thP μ (C S) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun S hS =>
    have := (thPMul F n μ _ _ (dom_monomial (g₂.1 S hS).2) (hA S hS)).1
    (thPMul F n μ _ _ this this).2.1
  have hCs : monomial (ν₁ + ν₂) * r * dPol n 1 = ∑ S ∈ (pairs n).powerset, sgS S • C S := by
    rw [← hv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [C, monomial_add, mul_smul_comm]
    congr 1
    ring
  have e1 : thP μ (monomial (ν₁ + ν₂) * dPol n t * r) = vPoly n t • ∑ S ∈ (pairs n).powerset,
      sgS S • groupConv μ (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) (th μ (ν₂ + eR S)) := by
    rw [mul_comm _ r, ← (thPMul F n μ _ _ hr (g₃.2.1 t)).2.2.2, ← hid, cv_smul_right]
    congr 1
    unfold sand
    rw [cv_sum_right μ _ hr' fun S hS => Submodule.smul_mem _ _ (groupConv_mem μ (hth _ (g₁.1 S hS).1)
      (groupConv_mem μ oneK_mem (hth _ (g₂.1 S hS).2)))]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [cv_smul_right, ← cv_assoc μ hr' (hth _ (g₁.1 S hS).1) (groupConv_mem μ oneK_mem (hth _ (g₂.1 S hS).2)),
      ← (thPMul F n μ _ _ hr (dom_monomial (g₁.1 S hS).1)).2.2.2, thP_monomial,
      cv_assoc μ (groupConv_mem μ hr' (hth _ (g₁.1 S hS).1)) oneK_mem (hth _ (g₂.1 S hS).2)]
  rw [e1, ← hsat, hCs, theta_sum₂, cv_sum_left μ _ oneK_mem fun S hS => Submodule.smul_mem _ _ (hC S hS),
    cv_sum_right μ _ oneK_mem fun S hS => groupConv_mem μ (Submodule.smul_mem _ _ (hC S hS)) oneK_mem,
    ← smul_sub, ← Finset.sum_sub_distrib]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun S hS => ?_)
  rw [cv_smul_left, cv_smul_right, ← smul_sub]
  refine Submodule.smul_mem _ _ ?_
  have hAm := (thPMul F n μ _ _ (hA S hS) (hA S hS)).2.1
  have hAK := groupConv_mem μ hAm (oneK_mem (F := F) (n := n))
  have hCK := groupConv_mem μ (hC S hS) (oneK_mem (F := F) (n := n))
  have m1 : groupConv μ (th μ (ν₂ + eR S)) (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) -
      groupConv μ (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) (th μ (ν₂ + eR S)) ∈ comm μ := by
    rw [th, cv_smul_left, cv_smul_right, ← smul_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, Or.inr ⟨_, (g₂.1 S hS).2, rfl⟩, hAK, rfl⟩)
  have m2 : groupConv μ (oneK F n) (groupConv μ (thP μ (C S)) (oneK F n)) -
      groupConv μ (groupConv μ (thP μ (C S)) (oneK F n)) (oneK F n) ∈ comm μ :=
    Submodule.subset_span ⟨_, _, Or.inl rfl, hCK, rfl⟩
  rw [cv_assoc μ (hC S hS) oneK_mem oneK_mem, oneK_mul μ hK] at m2
  rw [← cv_assoc μ (hth _ (g₂.1 S hS).2) hAm oneK_mem, ← thP_monomial μ (ν₂ + eR S),
    (thPMul F n μ _ _ (dom_monomial (g₂.1 S hS).2) (hA S hS)).2.2.2, thP_monomial] at m1
  have := Submodule.neg_mem _ (Submodule.add_mem _ m1 m2)
  convert this using 1
  simp only [C]
  abel
