import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCurve
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra

noncomputable section

namespace OrbitCurve

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def tDeg (ι : Type) [DecidableEq ι] : ι → ι → ℕ := fun k ↦ Pi.single k 1

omit [Fintype ι] in

theorem isWeightedHomogeneous_mConeMap (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f b) :
    IsWeightedHomogeneous (tDeg ι) (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) b := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  rw [Geo.mConeMap, aeval_monomial, Finsupp.prod, MvPolynomial.algebraMap_apply]
  have hb : b = 0 + ∑ p ∈ m.support, m p • tDeg ι p.1 := by
    rw [zero_add, ← hf (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum]
    rfl
  rw [hb]
  refine (isWeightedHomogeneous_C _ _).mul (IsWeightedHomogeneous.prod _ _ _ fun p _ ↦ ?_)
  have h := ((isWeightedHomogeneous_C (tDeg ι) (flatCone x p)).mul
    (isWeightedHomogeneous_X (AlgebraicClosure ℚ) (tDeg ι) p.1)).pow (m p)
  rwa [zero_add] at h

omit [Fintype ι] in

theorem mConeMap_weightedHomogeneousComponent (x : Cone n (AlgebraicClosure ℚ))
    (f : MvPolynomial (Coord n) ℤ) (b : ι → ℕ) :
    Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) b f) =
      weightedHomogeneousComponent (tDeg ι) b (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by
  classical
  conv_rhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum]
  have hom : ∀ a, IsWeightedHomogeneous (tDeg ι)
      (Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) a f)) a :=
    fun a ↦ isWeightedHomogeneous_mConeMap x (weightedHomogeneousComponent_isWeightedHomogeneous a f)
  rw [Finset.sum_eq_single b]
  · exact (IsWeightedHomogeneous.weightedHomogeneousComponent_same (hom b)).symm
  · intro a _ hab
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne b (hom a) (Ne.symm hab)
  · intro hb
    have h0 : weightedHomogeneousComponent (coordDeg n) b f = 0 := by
      by_contra h
      exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [h0, map_zero, map_zero]

omit [Fintype ι] [DecidableEq ι] in

theorem isPrime_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) : (orbitIdeal x).IsPrime :=
  RingHom.ker_isPrime _

omit [Fintype ι] in

theorem weightedHomogeneousComponent_mem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  rw [mConeMap_weightedHomogeneousComponent, hf, map_zero]

theorem isMultiHomogIdeal_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x) := by
  classical
  refine ⟨{f | f ∈ orbitIdeal x ∧ ∃ a, Geo.IsMultiHomog (ι := blockIdx n) f a}, fun f hf ↦ hf.2,
    le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.mpr fun f hf ↦ hf.1)⟩
  rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  refine Ideal.sum_mem _ fun m _ ↦
    Ideal.subset_span ⟨weightedHomogeneousComponent_mem_orbitIdeal x hf m, m, ?_⟩
  exact (geoMultiHomog_iff _ m).mpr (weightedHomogeneousComponent_isWeightedHomogeneous m f)

theorem isRelevant_orbitIdeal {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    Geo.IsRelevant (ι := blockIdx n) (orbitIdeal x) := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine fun k ↦ ⟨c k, fun h ↦ ?_⟩
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X] at h
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) h

omit [Fintype ι] [DecidableEq ι] in

theorem isHorizontal_orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsHorizontal (ι := blockIdx n) (orbitIdeal x) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  change aeval _ (C a) = 0 ↔ a = 0
  rw [aeval_C]
  exact map_eq_zero_iff _ (RingHom.injective_int _)

def coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    MvPolynomial (Coord n) ℚ →ₐ[ℚ] MvPolynomial ι (AlgebraicClosure ℚ) :=
  aeval fun p ↦ C (flatCone x p) * X p.1

omit [Fintype ι] [DecidableEq ι] in
theorem coneMapQ_map (x : Cone n (AlgebraicClosure ℚ)) (f : MvPolynomial (Coord n) ℤ) :
    coneMapQ x (map (Int.castRingHom ℚ) f) = Geo.mConeMap (ι := blockIdx n) (flatCone x) f := by
  rw [← algebraMap_int_eq, coneMapQ, aeval_map_algebraMap]
  rfl

omit [Fintype ι] [DecidableEq ι] in

theorem comap_ker_coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    (RingHom.ker (coneMapQ x)).comap (map (Int.castRingHom ℚ)) = orbitIdeal x := by
  ext f
  rw [Ideal.mem_comap, RingHom.mem_ker, coneMapQ_map, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]

omit [DecidableEq ι] in

theorem ker_coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    RingHom.ker (coneMapQ x) = ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤ RingHom.ker (coneMapQ x) :=
    Ideal.map_le_iff_le_comap.mpr (comap_ker_coneMapQ x).ge
  refine (eq_of_le_of_not_lt hle fun hlt ↦ ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, comap_ker_coneMapQ] at h
  exact lt_irrefl _ h

omit [Fintype ι] [DecidableEq ι] in

theorem algebraicIndependent_C_mul_X (a : ι → AlgebraicClosure ℚ) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent ℚ (fun k ↦ (C (a k) * X k : MvPolynomial ι (AlgebraicClosure ℚ))) := by
  let φ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k) * X k
  let ψ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  have hφ : Function.Injective φ := Function.LeftInverse.injective (g := ψ) fun p ↦ by
    rw [← AlgHom.comp_apply, hψφ, AlgHom.id_apply]
  have h := ((MvPolynomial.algebraicIndependent_X ι (AlgebraicClosure ℚ)).map' hφ).restrictScalars
    (R := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  convert h using 1
  funext k
  simp [φ]

theorem trdeg_range_coneMapQ {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    trdeg ℚ (coneMapQ x).range = Fintype.card ι := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine le_antisymm ?_ ?_
  · calc trdeg ℚ (coneMapQ x).range ≤ trdeg ℚ (MvPolynomial ι (AlgebraicClosure ℚ)) :=
          trdeg_le_of_injective (coneMapQ x).range.val Subtype.val_injective
      _ = Fintype.card ι := by
          have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
          rw [← trdeg_add_eq ℚ (AlgebraicClosure ℚ) (A := MvPolynomial ι (AlgebraicClosure ℚ)),
            trdeg_eq_zero, MvPolynomial.trdeg_of_isDomain]
          simp
  · let u : ι → (coneMapQ x).range := fun k ↦
      ⟨C (x k (c k)) * X k, ⟨X ⟨k, c k⟩, by simp [coneMapQ, flatCone]⟩⟩
    have hu : AlgebraicIndependent ℚ u :=
      AlgebraicIndependent.of_comp (coneMapQ x).range.val (algebraicIndependent_C_mul_X _ hc)
    simpa using hu.cardinalMk_le_trdeg

theorem ringKrullDim_quot_ker_coneMapQ {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℚ ⧸ RingHom.ker (coneMapQ x)) = Fintype.card ι := by
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMapQ x)).toRingEquiv]
  have : Algebra.FiniteType ℚ (coneMapQ x).range :=
    Algebra.FiniteType.of_surjective (coneMapQ x).rangeRestrict (coneMapQ x).rangeRestrict_surjective
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℚ, trdeg_range_coneMapQ hx]
  simp

theorem ringKrullDim_orbitIdeal {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ orbitIdeal x) =
      ((1 + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
  have := isPrime_orbitIdeal x
  have hz : ∀ m : ℤ, (C m : MvPolynomial (Coord n) ℤ) ∈ orbitIdeal x → m = 0 := fun m hm ↦ by
    have h : m ∈ (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hm
    rwa [show (orbitIdeal x).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from
      isHorizontal_orbitIdeal x, Ideal.mem_bot] at h
  obtain ⟨-, -, h⟩ := ReciprocityTheory.AnForm.R.extQ_spec (orbitIdeal x) hz
  rw [← h, ← ker_coneMapQ, ringKrullDim_quot_ker_coneMapQ hx, Nat.cast_add, Nat.cast_one, add_comm]

end OrbitCurve

theorem OrbitCurve.full : OrbitCurve.Statement := by
  intro ι _ _ _ n x hx
  exact ⟨inferInstance, ⟨OrbitCurve.isPrime_orbitIdeal x, OrbitCurve.isMultiHomogIdeal_orbitIdeal x,
    OrbitCurve.isRelevant_orbitIdeal hx⟩, OrbitCurve.isHorizontal_orbitIdeal x,
    OrbitCurve.ringKrullDim_orbitIdeal hx⟩

end

end GroundTheory.Heights₂.Heights
