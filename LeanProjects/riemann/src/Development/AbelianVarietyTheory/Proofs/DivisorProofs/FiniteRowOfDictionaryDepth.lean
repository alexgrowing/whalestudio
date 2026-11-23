import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralRatioOfHyp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open GlobalTheory.SumSize

namespace GlobalTheory.SumSize

theorem finRowK (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hD : DictK) (hd : DepthK) : FinRowK := by
  have hG : PairInt.PairIntRatK := GlobalTheory.T.pair_integral_ratio_of_norm_sums hP hI hD
  obtain ⟨CF0, h⟩ := BigC.and hG hd
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨dl, hL, h⟩, hDe⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  refine ⟨dl, hL, ?_⟩
  intro t w hw Φ β d hO c i a v hv
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hO
  have hrat := (h3.isRatAt hβ hτ hdτ c).2 i
  obtain ⟨hk, ⟨e, -, hPz, -⟩, hcos⟩ := hτ
  have hdep := (hDe t Φ β hβ).2
  exact h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1
    (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv

end GlobalTheory.SumSize

end
