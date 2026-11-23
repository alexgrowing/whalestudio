import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.SumEqCardMulSub
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.RatioEqOneOfAltSum
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem lemmaX : PositivityTheory.Lit1.GEN.GlobalEulerCharCoprime := by
  intro K S hS ℓ _ hℓS L _ hL hPn hcop hζ hK ιr M _ _ hMl hMP
  have : Finite S := hS
  refine ratio_eq_one_of_altSum hℓS ιr M hMl ?_
  have : Finite (zmodRepOfTorsion ℓ M hMl) := ‹Finite M›
  have : Module.Finite (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) := Module.Finite.of_finite
  exact altSum hL hℓS hPn hcop hζ hK ιr (zmodRepOfTorsion ℓ M hMl) (fun g m => by
    have := congrArg (fun f => f m) (hMP g g.2)
    exact this)

end PositivityTheory.Lit1.GEN.X
