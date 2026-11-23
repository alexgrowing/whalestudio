import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

noncomputable section

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) : coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · have h := (hF.1.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = derivative ℂ_[p] (GL3Theta.ser1 lam F) := by
  ext n
  rw [coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, taylorCoeffAtZero_deriv]
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  rw [ha]
  have e : ((n : ℂ) + 1) * (a (n + 1) : ℂ) = ((((n : Qbar) + 1) * a (n + 1) : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul, map_add, map_natCast, map_one,
    mul_comm]

theorem atU_deriv (g : GL3Theta.G1 p) {F : ℂ → ℂ} (hF : AlgEnt F) :
    derivative ℂ_[p] (g.atU F) =
      g.atU (deriv F) * (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * derivative ℂ_[p] g.l) := by
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, derivative_subst hs, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem bddSer_derivative {f : PowerSeries ℂ_[p]} (hf : BddSer f) : BddSer (derivative ℂ_[p] f) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  rw [coeff_derivative, norm_mul]
  have h1 : ‖((n : ℂ_[p]) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  calc _ ≤ B * 1 := mul_le_mul (hB _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = B := mul_one B

end GlobalTheory.ThetaTransl.CubeSer

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem sqThD_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  intro p _ g hOk hL h2 h3 hd hσ v hv hw
  obtain ⟨-, hwi, -, -, hA⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hOk hL h2 h3 hd
  have hq : IsWq g.W g.wq := hOk.2.1
  obtain ⟨hS, hB⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hmul, hconst, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨i1, i2, i3, i4, i6, -⟩ := hOk.1
  obtain ⟨vI, hvI, hvl⟩ := PI.JetsPhW.Inv.inverse_omega_holds p g.W g.wq i1 i2 i3 i4 i6 hq
  rw [PI.JetsPhW.Inv.dX_eq_derivative] at hvl
  change vI * derivative ℂ_[p] g.l = 1 at hvl
  have hσd := algEnt_deriv hσ
  have hSd := algEnt_deriv hS
  have hm2 : (((-2 : Qbar)) : ℂ) = -2 := by push_cast; rfl
  have hc := hconst (((-2 : Qbar)) : ℂ) (-2 : Qbar).2
  have hl2 : lamC g.lam (((-2 : Qbar)) : ℂ) = -2 := by
    rw [GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  have k1 := (hmul (sgStar g.abelian₂) (deriv (sqTh g.abelian₂ v)) hσ hSd).1
  have k2 := (hmul (deriv (sgStar g.abelian₂)) (sqTh g.abelian₂ v) hσd hS).1
  have k3 := (hmul (fun _ => (((-2 : Qbar)) : ℂ)) (fun z => deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)
    hc.1 k2.1).1
  have k4 := (hmul (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z)
    (fun z => (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) k1.1 k3.1).2
  have hT : sqThD g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z) := by
    funext z
    rw [hm2]
    simp only [sqThD]
    ring
  refine ⟨hT ▸ k4.1, ?_⟩
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  set L := lineSer g.wq⁻¹ (xAt g v) with hL'
  obtain ⟨-, hbdd, hCb, hX, -⟩ := SerRing.series_ring_laws p
  refine ⟨vI * (X * derivative ℂ_[p] L - 2 * L), ?_, ?_⟩
  · have hX2 : BddSer (X ^ 2 : PowerSeries ℂ_[p]) := by
      rw [pow_two]; exact (hbdd _ _ ⟨1, hX⟩ ⟨1, hX⟩).2.2
    have hLb : BddSer L := by
      rw [hL', lineSer]; exact (hbdd _ _ ⟨1, hwi⟩ (hbdd _ _ (hCb _).1 hX2).2.2).2.1
    have h2b : BddSer (2 : PowerSeries ℂ_[p]) := by
      rw [show (2 : PowerSeries ℂ_[p]) = C 2 from (map_ofNat C 2).symm]; exact (hCb 2).1
    refine (hbdd _ _ ⟨1, fun n => hvI n⟩ (hbdd _ _ ((hbdd _ _ ⟨1, hX⟩ (bddSer_derivative hLb)).2.2)
      ((hbdd _ _ h2b hLb).2.2)).2.1).2.2
  · have dA := atU_deriv g hσ
    have dB := atU_deriv g hS
    rw [hA] at dA
    rw [hB] at dB
    have hDA : derivative ℂ_[p] (C ε * X * e) = C ε * (e + X * derivative ℂ_[p] e) := by
      simp only [Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul]
      ring
    have hDB : derivative ℂ_[p] (e ^ 2 * L) =
        2 * e * derivative ℂ_[p] e * L + e ^ 2 * derivative ℂ_[p] L := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hDA] at dA
    rw [hDB] at dB
    have F4 : C ε * C ε⁻¹ = (1 : PowerSeries ℂ_[p]) := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero _), map_one]
    set a1 := g.atU (deriv (sgStar g.abelian₂))
    set b1 := g.atU (deriv (sqTh g.abelian₂ v))
    set x := C ε
    set y := C ε⁻¹
    set l' := derivative ℂ_[p] g.l
    set E' := derivative ℂ_[p] e
    set L'' := derivative ℂ_[p] L
    have ha1 : a1 = (e + X * E') * vI := by
      linear_combination (-a1) * F4 + (-a1 * x * y) * hvl + (-y * vI) * dA + ((e + X * E') * vI) * F4
    have hb1 : b1 = y * (2 * e * E' * L + e ^ 2 * L'') * vI := by
      linear_combination (-b1) * F4 + (-b1 * x * y) * hvl + (-y * vI) * dB
    have hT' : g.atU (sqThD g.abelian₂ v) = x * X * e * b1 + C (-2) * (a1 * (e ^ 2 * L)) := by
      rw [← hA, ← hB, ← hl2]
      calc g.atU (sqThD g.abelian₂ v) = g.atU (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
            (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) := by rw [← hT]
        _ = _ := by rw [k4.2, k1.2, k3.2, k2.2, hc.2]
    rw [hT', show (C (-2) : PowerSeries ℂ_[p]) = -2 by rw [map_neg, map_ofNat]]
    linear_combination (x * X * e) * hb1 - (2 * e ^ 2 * L) * ha1 +
      (X * e * (2 * e * E' * L + e ^ 2 * L'') * vI) * F4

end GlobalTheory.ThetaTransl.CubeSer
