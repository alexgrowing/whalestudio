import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain

theorem UpperTheory.V.Z.Win.Birth.prOrd :
    UpperTheory.V.Z.Win.Birth.PrOrd := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h
  refine ⟨π, h.reg, h.att, fun v => ?_⟩
  by_cases hB : ∃ B, π.HasSat v B
  · exact Or.inr hB
  · exact Or.inl fun σ hσ =>
      (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r h v σ hσ).resolve_right hB
