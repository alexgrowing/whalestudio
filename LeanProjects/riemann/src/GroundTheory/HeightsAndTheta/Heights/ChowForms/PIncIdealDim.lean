import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealDim.proof (h₁ : IncidenceGeneric.Statement) (h₂ : GenericLinearTrdeg.Statement)
    (h₃ : AffineChartTrdeg.Statement) : IncIdealDim.Statement := by
  intro F _ n k d P hP hdim
  have := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set K := FractionRing (MvPolynomial (Fin (n' + 1)) F ⧸ P)
  set ξ := genPt P
  have hξj : ξ j ≠ 0 := by
    simp only [ξ, genPt]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin (n' + 1) → K := fun m => if m = j then (ξ j)⁻¹ else 0 with hc_def
  have hc : ∑ m, c m * ξ m = 1 := by
    simp [c, inv_mul_cancel₀ hξj]

  let τ : Fin k × Fin n' → Fin k × Fin (n' + 1) := fun im => (im.1, j.succAbove im.2)
  have hτ : Function.Injective τ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [τ, Prod.mk.injEq] at h
    exact Prod.ext h.1 (j.succAbove_right_injective h.2)
  let ψ : MvPolynomial (Fin k × Fin n') K →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    (rename τ).restrictScalars F
  have hψ : Function.Injective ψ := rename_injective τ hτ
  let η : Fin n' → K := fun m => -(ξ (j.succAbove m) * (ξ j)⁻¹)
  let G : Set (MvPolynomial (Fin k × Fin n') K) :=
    Set.range (fun ij => X ij) ∪ Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))

  have hA : ∀ i m, genSubst ξ c (i, j.succAbove m) = ψ (X (i, m)) := by
    intro i m
    simp [ψ, τ, genSubst, c, Fin.succAbove_ne]
  have hB : ∀ i, genSubst ξ c (i, j) = ψ (∑ m, X (i, m) * C (η m)) := by
    intro i
    have h1 : (C (ξ j) * C (ξ j)⁻¹ : MvPolynomial (Fin k × Fin (n' + 1)) K) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hξj, map_one]
    have h2 : ψ (∑ m, X (i, m) * C (η m)) =
        -((∑ m, X (i, j.succAbove m) * C (ξ (j.succAbove m))) * C (ξ j)⁻¹) := by
      simp only [ψ, AlgHom.restrictScalars_apply, map_sum, map_mul, rename_X, rename_C, τ]
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [C_neg, C_mul]
      ring
    rw [h2]
    simp only [genSubst, c, if_pos rfl]
    rw [Fin.sum_univ_succAbove _ j]
    linear_combination (-(X (i, j) : MvPolynomial (Fin k × Fin (n' + 1)) K)) * h1
  have hrange : Set.range (genSubst ξ c) = ψ '' G := by
    ext p
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      by_cases hm : m = j
      · rw [hm]
        exact ⟨_, Or.inr ⟨i, rfl⟩, (hB i).symm⟩
      · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
        exact ⟨_, Or.inl ⟨(i, m'), rfl⟩, (hA i m').symm⟩
    · rintro ⟨q, (⟨⟨i, m⟩, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact ⟨(i, j.succAbove m), hA i m⟩
      · exact ⟨(i, j), hB i⟩

  have hη : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = ((d : ℕ) : Cardinal) := by
    have heq : Algebra.adjoin F (Set.range η) =
        Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹) := by
      apply le_antisymm
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        exact neg_mem (Algebra.subset_adjoin ⟨j.succAbove m, rfl⟩)
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        by_cases hm : m = j
        · beta_reduce
          rw [hm, mul_inv_cancel₀ hξj]
          exact one_mem _
        · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
          have : ξ (j.succAbove m') * (ξ j)⁻¹ = -η m' := (neg_neg _).symm
          beta_reduce
          rw [this]
          exact neg_mem (Algebra.subset_adjoin ⟨m', rfl⟩)
    rw [heq]
    exact h₃ F (n' + 1) d P j hP hdim hj

  let φ : MvPolynomial (Fin k × Fin (n' + 1)) F →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    aeval (genSubst ξ c)
  have hker : incIdeal P k = RingHom.ker φ := by
    ext g
    rw [h₁ F (n' + 1) k P c hc g, RingHom.mem_ker]
  have hφrange : φ.range = (Algebra.adjoin F G).map ψ := by
    show (aeval (genSubst ξ c)).range = _
    rw [aeval_range, hrange, Algebra.adjoin_image]
  haveI : Algebra.FiniteType F φ.range :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have htr : Algebra.trdeg F φ.range = ((k * n' + min k d : ℕ) : Cardinal) := by
    rw [hφrange, ← AlgEquiv.trdeg_eq (A := ↥(Algebra.adjoin F G))
      (Subalgebra.equivMapOfInjective (Algebra.adjoin F G) ψ hψ)]
    exact h₂ F K n' k d η hη
  rw [hker, ringKrullDim_eq_of_ringEquiv (AlgEquiv.toRingEquiv (Ideal.quotientKerEquivRange φ)),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := ↥φ.range), htr]
  have hnum : k * (n' + 1) - k + min k d = k * n' + min k d := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hnum]
  simp

end GroundTheory.Heights₂.Heights
