import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EabClass

theorem rdV_class {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {X : B.Mat k r}
    (hX : B.inLie k r X) {f : B.Mat k r → E} (hf : B.CkOn ⊤ (B.GV k r) f ∧ ∀ m : ℕ, B.InCC A m f) :
    B.CkOn ⊤ (B.GV k r) (RdV X f) ∧ ∀ m : ℕ, B.InCC A m (RdV X f) := by
  refine ⟨Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hf.1), fun m => ?_⟩
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (v := [X]) (by simpa using hX) (hf.2 _)

theorem eh_class : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  intro k r Wp Wq _ _ _ _ _ _ A a b f hf
  have h1 := rdV_class (X := hpart1 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _) hf
  have h2 := rdV_class (X := hpart2 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _) hf
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1.1 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul Complex.I h2.1), fun m => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h1.2 m
  obtain ⟨c₂, hc₂⟩ := h2.2 m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul Complex.I hc₂)⟩

end GlobalTheory.EabClass
