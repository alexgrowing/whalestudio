import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormFsvSubOnePow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDifferenceForm

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def DecayUnifOfParts : Prop := KB.RadHead → KB.HeadTop → WaveDiffForm → DecayUnif

def DecayUnifOfHeads : Prop := KB.RadHead → KB.HeadTop → DecayUnif

theorem decayUnifOfHeads : DecayUnifOfHeads := fun hRH hHT =>
  decayUnif_of hRH hHT Formalism.FourierDecayAlt.P.wave_difference_form

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_heads : Formalism.FourierDecayAlt.P.PBO.DecayUnifOfHeads := Formalism.FourierDecayAlt.P.PBO.decayUnifOfHeads
