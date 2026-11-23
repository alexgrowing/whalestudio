import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CoordCurveDegree
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra

namespace CoordCurveDegree

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def coneMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p ↦ C (y p) * X p.1

theorem coneMapQ_map (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    coneMapQ y (map (Int.castRingHom ℚ) f) = mConeMap y f := by
  rw [← algebraMap_int_eq, coneMapQ, aeval_map_algebraMap]
  rfl

theorem comap_ker_coneMapQ (y : (Σ k, ι k) → Ω) :
    (RingHom.ker (coneMapQ y)).comap (map (Int.castRingHom ℚ)) = mCoordIdeal y := by
  ext f
  rw [Ideal.mem_comap, RingHom.mem_ker, coneMapQ_map, mCoordIdeal, RingHom.mem_ker]

theorem X_mem_of_eq_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hy : y p = 0) :
    (X p : MRing ι) ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, hy, C_0, zero_mul]

theorem int_eq_zero {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∀ m : ℤ, (C m : MRing ι) ∈ mCoordIdeal y → m = 0 := fun m hm ↦ by
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at h

theorem ker_coneMapQ {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    RingHom.ker (coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by
  have := hP.2.1.1
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) (int_eq_zero hP)
  have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤ RingHom.ker (coneMapQ y) :=
    Ideal.map_le_iff_le_comap.mpr (comap_ker_coneMapQ y).ge
  refine (eq_of_le_of_not_lt hle fun hlt ↦ ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, comap_ker_coneMapQ] at h
  exact lt_irrefl _ h

theorem trdeg_range {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    (trdeg ℚ (coneMapQ y).range).toENat = Fintype.card K := by
  have := hP.2.1.1
  obtain ⟨-, -, h⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) (int_eq_zero hP)
  have hd := hP.2.2.2
  have : Algebra.FiniteType ℚ (coneMapQ y).range :=
    Algebra.FiniteType.of_surjective (coneMapQ y).rangeRestrict (coneMapQ y).rangeRestrict_surjective
  rw [← h, ← ker_coneMapQ hP,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMapQ y)).toRingEquiv,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℚ] at hd
  have h2 : (trdeg ℚ (coneMapQ y).range).toENat + 1 = (Fintype.card K : ℕ∞) + 1 := by
    have e : (((1 + Fintype.card K : ℕ)) : WithBot ℕ∞) = (((Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by
      push_cast; ring
    rw [e] at hd
    exact_mod_cast hd
  exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top) h2

theorem algebraicIndependent_C_mul_X (a : K → Ω) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent Ω (fun k ↦ (C (a k) * X k : MvPolynomial K Ω)) := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k ↦ C (a k) * X k
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k ↦ C (a k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  have hφ : Function.Injective φ := Function.LeftInverse.injective (g := ψ) fun p ↦ by
    rw [← AlgHom.comp_apply, hψφ, AlgHom.id_apply]
  convert (MvPolynomial.algebraicIndependent_X K Ω).map' hφ using 1
  funext k
  simp [φ]

theorem injective_subst (k₀ : K) :
    Function.Injective (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦
      X (Sum.inr ()) * X (Sum.inl k₀)) : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] MvPolynomial (K ⊕ Unit) ℚ) := by
  set L := FractionRing (MvPolynomial (K ⊕ Unit) ℚ)
  let f := algebraMap (MvPolynomial (K ⊕ Unit) ℚ) L
  have h0 : f (X (Sum.inl k₀)) ≠ 0 :=
    (map_ne_zero_iff f (IsFractionRing.injective _ L)).mpr (X_ne_zero _)
  let η : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] L :=
    aeval (Sum.elim (fun k ↦ f (X (Sum.inl k))) fun _ ↦ f (X (Sum.inr ())) / f (X (Sum.inl k₀)))
  have hη : η.comp (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦
      X (Sum.inr ()) * X (Sum.inl k₀))) = IsScalarTower.toAlgHom ℚ _ L := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases i with k | u
    · simp [η, f]
    · simp only [AlgHom.comp_apply, aeval_X, Sum.elim_inr, map_mul, η, Sum.elim_inl,
        IsScalarTower.coe_toAlgHom']
      rw [div_mul_cancel₀ _ h0]
  intro a b hab
  apply IsFractionRing.injective (MvPolynomial (K ⊕ Unit) ℚ) L
  have := congrArg η hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hη] at this
  exact this

theorem isAlgebraic_ratio {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) : IsAlgebraic ℚ (y p / y ⟨p.1, c p.1⟩) := by
  by_contra hr
  set r := y p / y ⟨p.1, c p.1⟩
  set u : K → MvPolynomial K Ω := fun k ↦ C (y ⟨k, c k⟩) * X k
  have hu := algebraicIndependent_C_mul_X _ hc
  have hr1 : AlgebraicIndependent ℚ (fun _ : Unit ↦ r) := algebraicIndependent_unique_type_iff.mpr hr
  have h1 := AlgebraicIndependent.sumElim_comp hr1 hu

  set v : K ⊕ Unit → MvPolynomial K Ω := Sum.elim u fun _ ↦ C (y p) * X p.1
  have hv : AlgebraicIndependent ℚ v := by
    rw [algebraicIndependent_iff_injective_aeval] at h1 ⊢
    have e : (aeval v : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] _) =
        (aeval (Sum.elim u (algebraMap Ω (MvPolynomial K Ω) ∘ fun _ : Unit ↦ r))).comp
          (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦ X (Sum.inr ()) * X (Sum.inl p.1))) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      rcases i with k | w
      · simp [v]
      · simp only [v, u, r, AlgHom.comp_apply, aeval_X, Sum.elim_inr, Sum.elim_inl, map_mul,
          Function.comp_apply, MvPolynomial.algebraMap_eq]
        rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc p.1)]
    rw [e, AlgHom.coe_comp]
    exact h1.comp (injective_subst p.1)

  let w : K ⊕ Unit → (coneMapQ y).range := fun i ↦ ⟨v i, by
    rcases i with k | w
    · exact ⟨X ⟨k, c k⟩, by simp [coneMapQ, v, u]⟩
    · exact ⟨X p, by simp [coneMapQ, v]⟩⟩
  have hw : AlgebraicIndependent ℚ w := AlgebraicIndependent.of_comp (coneMapQ y).range.val hv
  have hle : Cardinal.toENat (Cardinal.mk (K ⊕ Unit)) ≤ Cardinal.toENat (trdeg ℚ (coneMapQ y).range) :=
    Cardinal.toENat.monotone' hw.cardinalMk_le_trdeg
  rw [trdeg_range hP] at hle
  simp only [Cardinal.mk_fintype, map_natCast] at hle
  have h' : Fintype.card (K ⊕ Unit) ≤ Fintype.card K := by exact_mod_cast hle
  rw [Fintype.card_sum, Fintype.card_unit] at h'
  omega

theorem isAlgebraic_blockFnField {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    Algebra.IsAlgebraic ℚ (blockFnField y) := by
  classical
  choose c hc using hP.2.1.2.2
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h ↦ hc k (X_mem_of_eq_zero h)
  refine IntermediateField.isAlgebraic_adjoin fun t ⟨p, q, hpq, ht⟩ ↦ ?_
  subst ht
  by_cases hq : y q = 0
  · rw [hq, div_zero]
    exact isIntegral_zero
  have hd : ∀ k', y ⟨k', Function.update c q.1 q.2 k'⟩ ≠ 0 := by
    intro k'
    by_cases h : k' = q.1
    · subst h; simpa using hq
    · simpa [Function.update_of_ne h] using hc' k'
  have e : (⟨p.1, Function.update c q.1 q.2 p.1⟩ : Σ k, ι k) = q := by
    obtain ⟨k, i⟩ := p
    obtain ⟨k', j⟩ := q
    simp only at hpq
    subst hpq
    simp
  have := isAlgebraic_ratio hP (Function.update c q.1 q.2) hd p
  rw [e] at this
  exact this.isIntegral

end CoordCurveDegree

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
