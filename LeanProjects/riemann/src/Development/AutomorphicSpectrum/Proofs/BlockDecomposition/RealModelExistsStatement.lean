import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.modelEx_main | exact GlobalTheory.CompanionTheory.ModelS.modelEx_main | (intros; apply GlobalTheory.CompanionTheory.ModelS.modelEx_main <;> assumption)
