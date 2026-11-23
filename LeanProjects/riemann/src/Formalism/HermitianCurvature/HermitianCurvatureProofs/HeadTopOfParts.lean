import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadVectorOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart

namespace Formalism.FourierDecayAlt.P

def PBI.HeadTopOfParts : Prop := PBI.HighestUnipotentIntegral → PBI.Exh → PBI.HeadWeightAt → KB.HeadTop

theorem head_top_of_parts : PBI.HeadTopOfParts := fun hU5 hExh hW =>
  head_top_of_correspondence (head_correspondence_of_parts levFrameExists_statement (head_vector_of_parts hU5 hExh)
    (head_types_of_types_at (head_types_at_of_weight hW)))

end Formalism.FourierDecayAlt.P
