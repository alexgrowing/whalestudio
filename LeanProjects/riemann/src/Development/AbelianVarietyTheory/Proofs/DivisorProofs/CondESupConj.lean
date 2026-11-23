import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem condE_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), condE P ⊔ D.host.conj • condE P = ⊤ := by
  intro D T L P
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hne : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, (P.w v).asIdeal ≠ D.host.conj • (P.w v').asIdeal := by
    intro v hv v' hv' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv (P.w v') (P.w v) := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    by_cases e : v' = v
    · subst e
      obtain ⟨f, hf⟩ := P.w_split v' hv'
      exact GlobalTheory.GridChars.not_conjPl_self hf hcc hc
    · apply e
      have h1 := (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D)
        (P.w v') (P.w v)).2 (Or.inr hc)
      rw [P.under_w hv, P.under_w hv'] at h1
      exact h1.symm
  have hmax' : ∀ v, (D.host.conj • (P.w v).asIdeal).IsMaximal := by
    intro v
    have := (P.w v).isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v).ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  rw [condE, Finset.smul_prod']
  simp only [smul_pow']
  refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun v' hv' => ?_
  exact Ideal.pow_sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal (hmax' v') (hne v hv v' hv'))

end GlobalTheory.FunObj.SqNum
