import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLj
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem chain_norm_of_sixth (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : MemberChainIntegral D := h6

theorem pairing_integrality_both_sides (Dx : DivX D) (T : TwForms D) : PairingFromIntegrality D Dx T := fun h6 h6T hp hpT =>
  ⟨fun hD => ⟨fun u w _ => pairing_lift_valuation_bound hD h6 hp u w, fun u μ _ hμ w _ hQ => pairTw_of hD h6T hpT u μ hμ w hQ⟩,
   fun hD => ⟨fun u w _ => pairing_lift_valuation_bound hD h6 hp u w, fun u μ hμ w _ hQ => pairTw_of hD h6T hpT u μ hμ w hQ⟩⟩

theorem levelColumn_of_sharpBound {Dx : DivX D} {T : TwForms D} (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (hTw : LevelPrimeColumnOtherTuples D Dx T) :
    ValuationAtLevelPrime D Dx T := fun u w hw μ hQ x hx =>
  ⟨fun _ => ColGe0_atT D u (h5 u) w hw x hx, fun hμ => hTw u w hw μ hμ hQ x hx⟩

theorem periodBound_at_level_of_twisted {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) (hE : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L)
    (hN : NuAtTDef D L) (hG : LevelPrimeCoprimeStabiliser D) (hp : PeriodClassSumWeyl D) (h6T : TwistedChainIntegral D T) (hpT : TwistedPeriodIntegral D Dx T)
    (hTw : LevelPrimeColumnOtherTuples D Dx T) (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : PeriodBoundAtLevelPrime D L :=
  period_integral_at_levelPrime (pairing_integrality_both_sides Dx T h6 h6T hp hpT).2 hD hE hN hG (levelColumn_of_sharpBound h5 hTw)

theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

theorem gains_losses_eq_defined (Gi : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (X : ErrX D) (c : ErrC)
    (hF : ∀ w, Formalism.MainNotions.G.ParametersFill Gi K w) (hE : L.EDef X K c) : Formalism.MainNotions.LocalQuadraticParts.ZeroGainAbove L := stmtZ Gi K X c hF hE

end Formalism.MainNotions.J

end
