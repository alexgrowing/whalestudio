import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitNodeEmbedding
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_node_embedding : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  first | exact @GlobalTheory.CompanionTheory.TreeNode.nodeEmb | exact GlobalTheory.CompanionTheory.TreeNode.nodeEmb | (intros; apply GlobalTheory.CompanionTheory.TreeNode.nodeEmb <;> assumption)
