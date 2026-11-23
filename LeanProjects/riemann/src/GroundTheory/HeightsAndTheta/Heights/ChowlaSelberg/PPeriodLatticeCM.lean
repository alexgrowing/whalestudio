import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PeriodLatticeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic Module
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem PeriodLatticeCM.proof (S : PrimeDiscriminant K) (F : CMFamily K) :
    PeriodLatticeCM.Statement S F := by
  intro s
  have := S.isTotallyComplex
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨I, c, hc, h⟩ := CMFamily.exists_periodLattice_eq S F s
  let P := idealPeriodPair (F.restrict s) hK I
  let L' : PeriodPair :=
    { ω₁ := c * P.ω₁
      ω₂ := c * P.ω₂
      indep := by
        have := P.indep
        rw [LinearIndependent.pair_iff] at this ⊢
        intro a b hab
        apply this a b
        have hab' : c * (a • P.ω₁ + b • P.ω₂) = 0 := by
          rw [← hab]; simp only [Complex.real_smul]; ring
        exact (mul_eq_zero.1 hab').resolve_left hc }
  have hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice := by
    ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by ring⟩
  refine ⟨L', ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [hlat, h, lattice_idealPeriodPair]
  · rw [latticeEnd_eq_of_homothetic hc hlat]
    exact latticeEnd_idealPeriodPair (F.restrict s) hK I

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
