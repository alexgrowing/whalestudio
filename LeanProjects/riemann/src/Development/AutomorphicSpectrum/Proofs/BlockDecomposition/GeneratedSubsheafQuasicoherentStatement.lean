import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherent
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_quasicoherent : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), (genSub hH n b : X.Modules).IsQuasicoherent := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | exact GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub <;> assumption)
