import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaSeparates

theorem eq_zero_of_thetaSum_rho : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Φ hΦ h
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  obtain ⟨𝓕₁, hF, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain F (Fin n × Fin d) μ inferInstance
  funext x
  have hP := GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ)
    (Fin n × Fin d) μ inferInstance 𝓕₁ hF htop Φ hΦ x
  have hz : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = 0 := by
    intro y
    have := h (M.co.e.symm (x, y))
    simpa [GlobalTheory.WeilM.Darboux.rho] using this
  simp only [hz, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, MeasureTheory.lintegral_zero] at hP
  have hs := (mul_eq_zero.mp hP.symm).resolve_left h0
  have h1 := ENNReal.tsum_eq_zero.mp hs 0
  have e : ((fun _ => (0 : AF F)) : Fin n × Fin d → AF F) + x = x := zero_add x
  simp only [map_zero, enorm_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h1
  simpa [e] using h1

end GlobalTheory.ThetaSeparates
