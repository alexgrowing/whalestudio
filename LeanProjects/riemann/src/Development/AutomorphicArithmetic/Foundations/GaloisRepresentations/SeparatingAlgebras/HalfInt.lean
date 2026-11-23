import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_shift {n : ℕ} (c : ℤ) (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) :
    pt ((fun i : Fin n => (c - ((i : ℕ) : ℤ)) • s) + θ) =
      fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i := by
  funext i
  simp only [pt, Pi.add_apply, AddCircle.toCircle_add, AddCircle.toCircle_zsmul, map_mul, map_zpow]

private lemma prod_zpow_sum {ι : Type*} (S : Finset ι) (u : ℂˣ) (f : ι → ℤ) :
    ∏ i ∈ S, u ^ f i = u ^ ∑ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private lemma monoChar_shift {n : ℕ} (l : Fin n → ℤ) (c : ℤ) (m : ℕ)
    (hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) (u : ℂˣ) :
    monomialChar l (fun i : Fin n => u ^ (c - ((i : ℕ) : ℤ))) = (u : ℂ) ^ m := by
  rw [monomialChar_apply, ← Units.coe_prod]
  have h : ∏ i : Fin n, (u ^ (c - ((i : ℕ) : ℤ))) ^ l i = u ^ (m : ℤ) := by
    rw [← hm, ← prod_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, mul_comm]
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val]

private lemma key {n : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hM : MeanVal) (hD : DensCont)
    (l : Fin n → ℤ) (c : ℤ) (m : ℕ) (hcm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) :
    ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * half (t : ℂ) (pt θ) =
      ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * (if m = 0 then 1 else 0) := by
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨hhalf, -, hev, hnorm⟩ := hD n t ht0 ht1
  have hmono : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have h := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using h
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hFc : Continuous F := hmono.mul hhalf
  let a : UnitAddCircle → Fin n → UnitAddCircle := fun s i => (c - ((i : ℕ) : ℤ)) • s
  have ha : Continuous a := continuous_pi fun i => continuous_zsmul _
  have hshift : ∀ s, ∫ θ, F (a s + θ) = ∫ θ, F θ := fun s => integral_add_left_eq_self F (a s)
  have hG : Continuous (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ)) :=
    hFc.comp ((ha.comp continuous_fst).add continuous_snd)
  have hint : Integrable (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ))
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Fin n → UnitAddCircle))) :=
    hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ θ, F θ = ∫ s : UnitAddCircle, ∫ θ, F (a s + θ) := by
    simp only [hshift, integral_const, probReal_univ, one_smul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  have hpt : ∀ s, pt (a s + θ) = (fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ))) * pt θ := by
    intro s
    rw [pt_shift]
    rfl
  simp only [hF, hpt, map_mul, monoChar_shift l c m hcm]
  have hz := hM n t ht0 ht1 (pt θ) (hnorm θ) c m
  have hcoe : ∀ s : UnitAddCircle, ((Circle.toUnits (AddCircle.toCircle s) : ℂˣ) : ℂ) = (AddCircle.toCircle s : ℂ) :=
    fun s => rfl
  calc _ = ∫ s : UnitAddCircle, monomialChar l (pt θ) * ((AddCircle.toCircle s : ℂ) ^ m *
        half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i)) := by
        congr 1
        funext s
        rw [hcoe, mul_comm (_ ^ m), mul_assoc]
        rfl
    _ = _ := by rw [integral_const_mul, hz]

theorem UpperTheory.Gal.Gen.halfInt_pf :
    UpperTheory.Gal.Gen.WtPos → UpperTheory.Gal.Gen.MeanVal → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.HalfInt := by
  intro hW hM hD n t ht0 ht1 l hl
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  by_cases h0 : l = 0
  · subst h0
    rw [key t ht0 ht1 hM hD (0 : Fin n → ℤ) 0 0 (by simp)]
    simp [monomialChar_zero]
  · obtain ⟨c, hc⟩ := hW n l hl h0
    have hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = ((∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat : ℤ) :=
      (Int.toNat_of_nonneg hc.le).symm
    rw [key t ht0 ht1 hM hD l c _ hm]
    have hne : (∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat ≠ 0 := by omega
    simp [hne, h0]
