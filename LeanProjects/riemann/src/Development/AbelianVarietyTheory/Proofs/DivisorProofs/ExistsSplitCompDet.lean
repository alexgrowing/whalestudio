import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq.SplitDet

theorem exists_splitComp_det : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N}, k ∈ intG D N → CongOne D 𝔪 k →
    SuppSplit D (k : GL (Fin N) (AE D)) → ∃ x : (AE D)ˣ, IntU D x ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧
      x = Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) * sgU D x ∧
      (x : AE D) - 1 ∈ hatId D 𝔪 ∧ (x : AE D) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
  intro D N 𝔪 k hk hc hs
  have hint := (mem_intG k).1 hk
  have huO : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) ∈ OhE D :=
    VacMove.det_int D _ hint
  have hn := VacMove.det_norm D k
  have hm1 : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈ hatId D 𝔪 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hz : ∀ q : ℕ, q.Prime → InertQ D q →
      ZeroAt D q (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) :=
    fun q hq hi => GlobalTheory.VacuumScalar.zeroAt_det hq (hs q hq hi)
  set U := Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) with hU
  set u : AE D := (U : AE D) with hu
  have hm2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (GlobalTheory.FunObj.StdDatum.mul_mem_hatId huO (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1))
  obtain ⟨ε, hε, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have hεε : sgA D (sgA D ε) = ε := VacMove.sgA_sgA D ε
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hn
  let x : (AE D)ˣ := ⟨_, _, hx, by rw [mul_comm, hx]⟩
  have hxv : (x : AE D) = (1 - η) + η * u := rfl
  have hx1 : (x : AE D) - 1 = η * (u - 1) := by rw [hxv]; ring
  have hηO : η ∈ OhE D := VacMove.sgA_mem D hε
  have h0 : (1 - u) * (1 - (ε + η)) = 0 := by
    refine GlobalTheory.VacuumScalar.eq_zero_of_zeroAt _ fun q hq => ?_
    by_cases hi : InertQ D q
    · convert VacMove.zeroAt_mul D hq (hz q hq hi) (-(1 - (ε + η))) using 1
      ring
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
      ring
  refine ⟨x, ⟨?_, ?_⟩, fun q hq hi => ?_, ?_, ?_, ?_⟩
  · rw [hxv]; exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO huO)
  · change (1 - η) + η * v ∈ OhE D
    exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO (VacMove.sgA_mem D huO))
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (η * (u - 1)) using 1
    rw [hx1]
    linear_combination (-(u - 1)) * h2 + (-(u - 1)) * h1'
  · ext
    change (1 - η) + η * u = u * sgA D ((1 - η) + η * u)
    rw [map_add, map_mul, map_sub, map_one, hεε]
    linear_combination h0 - ε * hn
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm1
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm2

end GlobalTheory.FunObj.NormUniq.SplitDet
