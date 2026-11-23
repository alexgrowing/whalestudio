import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WigAtOmega

theorem wigUpper_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)),
    inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A →
    WigUpper z z' d (fun g : B.Mat k r => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hT hz' hT' hA g hg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WigSh.OmgNorm.omg_norm k r z z' g hz hT hz' hT' hg
  have h := hA.2.2.2 _ h1 h2
  rw [h3] at h
  exact h

end GlobalTheory.CompanionTheory.WigAtOmega
