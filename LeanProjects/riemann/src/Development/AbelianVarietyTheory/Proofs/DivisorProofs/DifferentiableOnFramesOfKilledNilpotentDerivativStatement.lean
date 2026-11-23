import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ), (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → (∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ, HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧ ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X, Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) → DifferentiableOn ℂ Q X.dom := by
  first | exact @GlobalTheory.HolRead.Holo.differentiableOn_of_killed | exact GlobalTheory.HolRead.Holo.differentiableOn_of_killed | (intros; apply GlobalTheory.HolRead.Holo.differentiableOn_of_killed <;> assumption)
