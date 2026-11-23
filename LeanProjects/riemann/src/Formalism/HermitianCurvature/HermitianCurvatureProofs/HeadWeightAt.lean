import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAtOfExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTypesAtOfWeight

namespace Formalism.FourierDecayAlt.P

theorem head_weight_at : PBI.HeadWeightAt := by
  intro Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF
  exact head_weight_at_of_exists Wp Wq P p w X μ L st ν'r m₀r hD hcut hLev x hx γ₀ hγG hζ hγF
    (fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF)

end Formalism.FourierDecayAlt.P
