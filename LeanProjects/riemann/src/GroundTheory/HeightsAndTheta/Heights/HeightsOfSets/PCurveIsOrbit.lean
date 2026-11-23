import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveIsOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace CurveIsOrbit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem component_mem {W : Ideal (MvPolynomial (Coord n) ℤ)}
    (hW : Geo.IsMultiHomogIdeal (ι := blockIdx n) W) {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ W)
    (m : ι → ℕ) : weightedHomogeneousComponent (coordDeg n) m f ∈ W := by
  classical
  obtain ⟨S, hS, rfl⟩ := hW
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule ℤ (coordDeg n)) :=
    Ideal.homogeneous_span _ _ fun g hg ↦ by
      obtain ⟨a, ha⟩ := hS g hg
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff g a).mp ha)⟩
  exact (mem_iff_weightedHomogeneousComponent_mem _ _ hh f).mp hf m

def toArithVariety {W : Ideal (MvPolynomial (Coord n) ℤ)}
    (hW : Geo.IsArithVar (ι := blockIdx n) W 1) : ArithVariety n where
  ideal := W
  isPrime := hW.2.1.1
  homogeneous _ hf m := component_mem hW.2.1.2.1 hf m
  relevant := hW.2.1.2.2
  horizontal a ha := by
    have h : a ∈ W.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := ha
    rwa [hW.2.2.1, Ideal.mem_bot] at h

theorem exists_algHom_algebraicClosure (B : Type*) [CommRing B] [Nontrivial B] [Algebra ℚ B]
    [Algebra.FiniteType ℚ B] : Nonempty (B →ₐ[ℚ] AlgebraicClosure ℚ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType ℚ (B ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)
  have : Module.Finite ℚ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : B ⧸ m →ₐ[ℚ] AlgebraicClosure ℚ).comp (Ideal.Quotient.mkₐ ℚ m)⟩

theorem eq_of_le_of_ringKrullDim_eq {R : Type*} [CommRing R] {W W' : Ideal R} [W.IsPrime]
    (hle : W ≤ W') {d : ℕ} (hW : ringKrullDim (R ⧸ W) = d) (hW' : ringKrullDim (R ⧸ W') = d) :
    W = W' := by
  by_contra hne
  obtain ⟨f, hfW', hfW⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hr : Ideal.Quotient.mk W f ∈ nonZeroDivisors (R ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  have hg : ∀ a ∈ Ideal.span {Ideal.Quotient.mk W f}, Ideal.Quotient.factor hle a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfW', mul_zero]
  have h2 : ringKrullDim (R ⧸ W') ≤ ringKrullDim ((R ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W f}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.lift_surjective_of_surjective _ hg (Ideal.Quotient.factor_surjective hle))
  have h3 := (add_le_add_left h2 1).trans h1
  rw [hW, hW'] at h3
  have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((d : ℕ) : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : d + 1 ≤ d := by exact_mod_cast h4
  omega

theorem full : CurveIsOrbit.Statement := by
  intro ι _ _ n W hW
  let P := toArithVariety hW
  obtain ⟨c, hc⟩ := P.exists_chart
  obtain ⟨ψ⟩ := exists_algHom_algebraicClosure (P.ChartAlg c)
  have hx := (mem_points_iff_le_orbitIdeal P _).mp (P.chartPoint_mem c hc ψ)
  refine ⟨P.chartPoint c ψ, hx.1, ?_⟩
  have : Nonempty ι := hW.1
  have : W.IsPrime := hW.2.1.1
  exact eq_of_le_of_ringKrullDim_eq hx.2 hW.2.2.2 (OrbitCurve.full ι n _ hx.1).2.2.2

end CurveIsOrbit

end

end GroundTheory.Heights₂.Heights
