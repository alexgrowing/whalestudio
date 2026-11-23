import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) → ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank), X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧ IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_ident_frame | exact GlobalTheory.CovTop.VolUp.exists_ident_frame | (intros; apply GlobalTheory.CovTop.VolUp.exists_ident_frame <;> assumption)
