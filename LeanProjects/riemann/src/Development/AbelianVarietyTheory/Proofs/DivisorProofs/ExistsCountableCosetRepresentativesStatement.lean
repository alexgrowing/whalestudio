import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCosetRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_coset_representatives : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  first | exact @GlobalTheory.CovTop.VolUp.Reps.exists_reps | exact GlobalTheory.CovTop.VolUp.Reps.exists_reps | (intros; apply GlobalTheory.CovTop.VolUp.Reps.exists_reps <;> assumption)
