import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLambdaShiftNonnegStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.ExpTie

theorem numSt : NumSt := by
  have H := atPts_and (atPts_and (atPts_and GlobalTheory.T.parameter_hypothesis_all_points GlobalTheory.T.parameter_large_all_points) (atPts_and GlobalTheory.T.parameter_large_all_points_bound GlobalTheory.T.parameter_height_lt_genus))
    (atPts_and GlobalTheory.T.lambda_prime_all_points GlobalTheory.T.weight_lambda_shift_nonneg)
  refine atPts_imp H fun Fm x hx i p h j => ?_
  obtain ⟨⟨⟨hH, hR⟩, ⟨hL, hB⟩⟩, ⟨hF, hW⟩⟩ := h
  obtain ⟨W, hOk, hlam, hbox, hT, hSp⟩ := hW j
  refine ⟨parOf (Fm.L x i) j, W, ?_, hH j, hL j, hOk, hR j⟩
  exact
    { k := rfl, m := rfl, t := rfl, f := rfl
      card := Nat.card_eq_fintype_card.trans (Fm.D x i).what₂.card_Tau
      Nr := rfl, x := rfl, log := rfl, b := rfl
      lam := hlam, forced := hF j, box := hbox, thick := hT, special := hSp, big := hB j }

end GlobalTheory.ExpTie

end
