import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul' {O σ : Type} [CommRing O] (i : σ) (f g : MvPowerSeries σ O) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + constantCoeff g * coeff (Finsupp.single i 1) f := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  ring

private noncomputable def lin {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] : (σ → Q) →+ (FA O wt →ₗ[O] Q) where
  toFun v :=
    { toFun := fun f => ∑ i, coeff (Finsupp.single i 1) (ser f) • v i
      map_add' := fun f g => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        simp [Finset.smul_sum, mul_smul] }
  map_zero' := by ext f; simp
  map_add' v w := by ext f; simp [Finset.sum_add_distrib]

private theorem lin_apply {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (f : FA O wt) :
    lin wt Q v f = ∑ i, coeff (Finsupp.single i 1) (ser f) • v i := rfl

private theorem lin_zA {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (i : σ) :
    lin wt Q v ((WPres.free O wt).zA i) = v i := by
  classical
  rw [lin_apply]
  have : ser ((WPres.free O wt).zA i) = (X i : MvPowerSeries σ O) := rfl
  rw [this, Finset.sum_eq_single i]
  · simp [coeff_X]
  · intro b _ hb
    rw [coeff_X, if_neg, zero_smul]
    intro h
    exact hb (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.length_le_cotLen_of_injective_tangent_map :
    LemmaM' → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ), j ≠ 0 →
        ∀ (κ : Type) (F : κ → FA O wt), (∀ k, F k ∈ Fgr O wt j) → ∀ c : O, c ≠ 0 →
        ∀ (M : Type) [AddCommGroup M] [Module O M] (d : M →+ (σ → O ⧸ Ideal.span {c})), Function.Injective d →
        (∀ μ i, wt i ≠ j → d μ i = 0) → (∀ μ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) • d μ i = 0) →
        Module.length O M ≤ cotLen (x0 O wt) (Fgr O wt) j F := by
  intro hM O _ _ _ _ σ _ wt j hj κ F hF c hc M _ _ d hd hwt hker
  classical
  let D : M →+ (FA O wt →ₗ[O] O ⧸ Ideal.span {c}) := (lin wt (O ⧸ Ideal.span {c})).comp d
  have hD : ∀ μ f, D μ f = ∑ i, coeff (Finsupp.single i 1) (ser f) • d μ i :=
    fun μ f => lin_apply wt _ (d μ) f
  have hwsingle : ∀ i : σ, (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
    intro i
    simp [Finsupp.weight_apply]
  refine hM O (FA O wt) ℤ (Fgr O wt) (x0 O wt) j ?_ κ F hF c hc M D ?_ ?_ ?_
  · intro f hf
    rw [weightedSeriesOrigin_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (mem_Fgr.mp hf) 0 (by simpa using hj.symm)
  · intro μ ν h
    apply hd
    funext i
    have h2 := congrArg (fun L : FA O wt →ₗ[O] O ⧸ Ideal.span {c} => L ((WPres.free O wt).zA i))
      (congrArg (fun T => T) h)
    simpa [D, lin_zA] using h2
  · intro μ k
    rw [hD]
    exact hker μ k
  · intro μ
    choose e he using fun i => Ideal.Quotient.mk_surjective (d μ i)
    let e' : σ → O := fun i => if wt i = j then e i else 0
    have he' : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (e' i) = d μ i := by
      intro i
      by_cases h : wt i = j
      · simp [e', h, he]
      · simp [e', h, hwt μ i h]
    refine ⟨lin wt O e', ?_, ?_, ?_⟩
    · intro f g
      have hs : ser (f * g) = ser f * ser g := rfl
      rw [lin_apply, lin_apply, lin_apply, weightedSeriesOrigin_apply, weightedSeriesOrigin_apply, hs]
      simp only [coeff_single_mul', smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · intro i' hi' f hf
      rw [lin_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : wt i = j
      · have h0 : coeff (Finsupp.single i 1) (ser f) = 0 := by
          refine (mem_Fgr.mp hf) _ ?_
          rw [hwsingle, h]
          exact fun e => hi' e.symm
        rw [h0, zero_smul]
      · simp [e', h]
    · intro f
      rw [hD, lin_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he' i, smul_eq_mul, map_mul, Algebra.smul_def]
      rfl
