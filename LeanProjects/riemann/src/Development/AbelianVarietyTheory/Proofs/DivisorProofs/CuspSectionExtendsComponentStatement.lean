import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionExtendsComponent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_section_extends_component : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ la : AllWt.Weight S.Dw, (∀ τ, Antitone (la τ)) → ∀ f, IsCuspSec Φ k la f → ∃ g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0), (Φ.C k).val g = f := by
  first | exact @GlobalTheory.CovHt.Link.exists_cusp_of_isCuspSec | exact GlobalTheory.CovHt.Link.exists_cusp_of_isCuspSec | (intros; apply GlobalTheory.CovHt.Link.exists_cusp_of_isCuspSec <;> assumption)
