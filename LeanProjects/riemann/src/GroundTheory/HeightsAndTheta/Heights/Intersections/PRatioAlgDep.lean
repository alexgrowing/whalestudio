import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace RatioAlgebraicDependence

variable {K : Type} {ι : K → Type} {d : ℕ}

def homog (c : ∀ k, ι k) (p : Fin d → Σ k, ι k) (f : MvPolynomial (Fin d) ℤ) : MvPolynomial (Σ k, ι k) ℤ :=
  ∑ m ∈ f.support, C (coeff m f) *
    ∏ j, X (p j) ^ m j * X ⟨(p j).1, c (p j).1⟩ ^ (f.totalDegree - m j)

theorem aeval_homog {F : Type} [Field F] [Algebra ℤ F] (c : ∀ k, ι k) (p : Fin d → Σ k, ι k)
    (f : MvPolynomial (Fin d) ℤ) (w : (Σ k, ι k) → F) (hw : ∀ j, w ⟨(p j).1, c (p j).1⟩ ≠ 0) :
    aeval w (homog c p f) = (∏ j, w ⟨(p j).1, c (p j).1⟩) ^ f.totalDegree *
      aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f := by
  classical
  have hsum : aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f =
      ∑ m ∈ f.support, aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [hsum, Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ j, m j ≤ f.totalDegree := fun j ↦
    (monomial_le_degreeOf j hm).trans (degreeOf_le_totalDegree f j)
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle j)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨(p j).1, c (p j).1⟩ ^ m j), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw j)),
    mul_comm]

end RatioAlgebraicDependence

open RatioAlgebraicDependence in

theorem RatioAlgDep.proof : RatioAlgDep.Statement := by
  intro K _ ι _ Q d c p hQ
  classical
  by_cases hX : ∃ k, (X ⟨k, c k⟩ : MRing ι) ∈ Q
  · obtain ⟨k, hk⟩ := hX
    refine ⟨1, one_ne_zero, fun z hz hzc ↦ absurd ?_ (hzc k)⟩
    simpa using hz _ hk
  push Not at hX
  obtain ⟨Ω, _, y, hy, hbir⟩ := HilbertSamuel.BirationalModelExists.proof K ι Q d hQ
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 ↦ hX k (by
    rw [← hy, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hQ
  have htr := ConeTrdeg.proof K ι Ω y hbir (fun k ↦ ⟨c k, hc k⟩) (hy ▸ hhor)
  rw [hy] at htr
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ Q) (CoordinateConeArithVar.algebraMap_injective Q hhor)
  rw [hdim, htr, map_add, map_natCast] at hA
  have hA' : ((d + Fintype.card K : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K + 1 := by exact_mod_cast hA
  have hlt : Algebra.trdeg ℤ Ω < d := by
    rw [← Cardinal.toENat_lt_natCast]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = n := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [hn] at hA' ⊢
    have : d + Fintype.card K = n + Fintype.card K + 1 := by exact_mod_cast hA'
    exact_mod_cast (by omega : n < d)
  have hdep : ¬ AlgebraicIndependent ℤ (fun j : Fin d ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) :=
    fun hind ↦ by
      have h := hind.cardinalMk_le_trdeg
      rw [Cardinal.mk_fin] at h
      exact absurd hlt (not_lt.2 h)
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨f, hf0, hfne⟩ := hdep

  have hH : homog c p f ∈ Q := by
    rw [← hy, mCoordIdeal, RingHom.mem_ker]
    set L := FractionRing (MvPolynomial K Ω)
    let φ : MvPolynomial K Ω →ₐ[ℤ] L :=
      { algebraMap (MvPolynomial K Ω) L with
        commutes' := fun n ↦ by simp }
    have hφ : Function.Injective φ := fun a b h ↦ IsFractionRing.injective (MvPolynomial K Ω) L h
    have hw : ∀ q : Σ k, ι k, y q ≠ 0 → φ (C (y q) * X q.1) ≠ 0 := fun q hq ↦ by
      rw [Ne, ← map_zero φ, hφ.eq_iff]
      exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)
    have hrat : ∀ j, φ (C (y (p j)) * X (p j).1) / φ (C (y ⟨(p j).1, c (p j).1⟩) * X (p j).1) =
        φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩)) := fun j ↦ by
      rw [div_eq_iff (hw _ (hc _)), ← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc _)]
    refine hφ ?_
    rw [map_zero, mConeMap, comp_aeval_apply, aeval_homog c p f _ (fun j ↦ hw _ (hc _))]
    simp only [hrat]
    let ψ : Ω →ₐ[ℤ] L := φ.comp (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω))
    have key : (aeval fun j ↦ φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩))) f =
        ψ (aeval (fun j ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) f) := by
      rw [comp_aeval_apply]
      rfl
    rw [key, hf0, map_zero, mul_zero]
  refine ⟨f, hfne, fun z hz hzc ↦ ?_⟩
  have h1 := hz _ hH
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_homog c p f z (fun j ↦ hzc _)] at h1
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact (mul_eq_zero.1 h1).resolve_left
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ hzc _))

end GroundTheory.Heights₂.Heights.Inter
