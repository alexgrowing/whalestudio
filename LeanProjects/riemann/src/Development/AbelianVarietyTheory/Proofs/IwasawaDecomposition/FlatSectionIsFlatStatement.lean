import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_isFlat : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag) (k : s.Comp) (τ : D.what₂.Tau), IsFlat (fl.C k) (DV.tauEmb D τ) (flatSec s fl k τ) := by
  first | exact @GlobalTheory.ShFam.Hor.isFlat_flatSec | exact GlobalTheory.ShFam.Hor.isFlat_flatSec | (intros; apply GlobalTheory.ShFam.Hor.isFlat_flatSec <;> assumption)
