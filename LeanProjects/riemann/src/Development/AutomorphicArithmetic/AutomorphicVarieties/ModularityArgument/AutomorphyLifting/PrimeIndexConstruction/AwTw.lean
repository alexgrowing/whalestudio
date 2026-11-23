import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist

theorem UpperTheory.V.Z.Win.Birth.awTw :
    UpperTheory.V.Z.Win.Birth.AwTw := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r κ hκ haut hW
  obtain ⟨_, art, χ, a, hart, -, hL⟩ := hκ
  obtain ⟨π, hreg, hatt⟩ := haut
  obtain ⟨t, ht⟩ := hW π hreg hatt
  obtain ⟨b, hb⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winTw F χ
  exact UpperTheory.V.Z.Win.Birth.awOne F Ω l n hn ι _ (π.twist χ)
    (UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL)
    ⟨t + b, fun v => hb n (by omega) π t v (ht v)⟩
