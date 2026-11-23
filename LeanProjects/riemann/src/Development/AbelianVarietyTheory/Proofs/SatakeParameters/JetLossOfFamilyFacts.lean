import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProofStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.LiftTypePrime.Jets (intAt_mul intAt_sum intAt_of_isIntegral isIntegral_exp)
open GlobalTheory.MomT.CosetSum

noncomputable section

namespace GlobalTheory.DatumJets

section Int

variable {p : ℕ} [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]}

end Int

section Idx

variable {X : Fields} {a b : ℕ}

end Idx

theorem map_jetSum {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA c : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hcA0 : 0 < cA) (hc0 : 0 < c) (Ξ : HomE X.E a b → X.K) {e : DVar X.Tau a b →₀ ℕ} (he : e ∈ RatIdx A S cA c N N' Ξ) :
    A.σ₀ (jetSum A S cA c N N' Ξ e) = (A.chiF a b N N')⁻¹ *
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => A.σ₀ (Ξ x) * jetC A.cD (A.thInd S N N' c x) e := by
  have := GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA0 hc0
  have := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  rw [jetSum, latSum, latSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) z = x
  by_cases h0 : Ξ x = 0
  · simp [h0]
  · have h := he x x.2 h0
    rw [map_mul, Amb.jetK, desc, dif_pos h, h.choose_spec]
    ring

end GlobalTheory.DatumJets
