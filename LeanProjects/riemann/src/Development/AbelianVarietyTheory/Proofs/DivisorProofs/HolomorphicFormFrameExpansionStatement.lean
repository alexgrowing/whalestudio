import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_form_frame_expansion : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (φ : GA D V → ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la τ (Fin.cast hr c) = w ρ c) → IsHolFor θ V x w φ → ∀ g : GA D V, ∃ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom ∧ (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → Q y = φ (g * u) := by
  first | exact @GlobalTheory.HolRead.AdExt.exists_extension | exact GlobalTheory.HolRead.AdExt.exists_extension | (intros; apply GlobalTheory.HolRead.AdExt.exists_extension <;> assumption)
