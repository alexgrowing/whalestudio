import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPolesStatement

namespace GlobalTheory

theorem doublingMethod_of_three : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation →
    GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.DoublingMethod :=
  fun hC hE hP => GlobalTheory.T.siegel_eisenstein_continuation_and_poles hC (fun D V h0 a ha hI μ b hμ hb s₁ φ hφ =>
    ⟨hE D V h0 a ha hI μ b hμ hb s₁ φ hφ, fun hab => hP D V h0 a ha hI μ b hμ hb s₁ φ hφ hab⟩)

end GlobalTheory
