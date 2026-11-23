import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionImageFinHomMulVec
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_completion_image_finHom_mulVec : ∀ (D : D7) (V : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) (δ : GL (Fin V.rank) D.host.E), (hat (maximalRealSubfield D.host.E) (L : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) = ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).mulVec '' (hat (maximalRealSubfield D.host.E) (Λ : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) → IsUStab (-(V.gram)ᵀ) L δ → ∃ γ ∈ GQ V, (∀ τ θ, IsInfEmb τ θ → infMat D.sp.cm.sig V.gram θ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ) ∧ IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (Λ : Set (Fin V.rank → D.host.E)) 1 ((finHom V (g⁻¹ * γ * g)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := by
  first | exact @GlobalTheory.CovTop.VolUp.RatStab.main | exact GlobalTheory.CovTop.VolUp.RatStab.main | (intros; apply GlobalTheory.CovTop.VolUp.RatStab.main <;> assumption)
