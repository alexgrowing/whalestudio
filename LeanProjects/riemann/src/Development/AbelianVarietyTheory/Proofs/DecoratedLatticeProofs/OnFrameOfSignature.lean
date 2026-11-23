import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
import Formalism.LocalRingCardinality.PosOfIsomEmb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

open scoped Matrix

namespace GlobalTheory.Core.Rk.Top.FockPair

variable {D : D7} {u : D.what₂.Word}

open Classical in

def bf {K : ClsPTied u} (V : ValPTied u K) : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ :=
  if h : ∃ c : (D.fm u).clsP, Nat.card ((D.fm u).stabilizer₂ c) ≠ 0 then
    ((Nat.card ((D.fm u).stabilizer₂ h.choose) : ℂ)) •
      (((D.fm u).ipP.comp (V.eW.symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ => FrP D → ℂ) h.choose)).compl₂
        (V.eW.symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ => FrP D → ℂ) h.choose))
  else 0

end GlobalTheory.Core.Rk.Top.FockPair

end
