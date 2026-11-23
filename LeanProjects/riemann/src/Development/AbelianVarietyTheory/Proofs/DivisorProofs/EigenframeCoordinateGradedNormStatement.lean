import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeCoordinateGradedNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_coordinate_graded_norm : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) (x : Sp K ⟶ (Φ.C k).Y.X) (F : (Φ.C k).Y.Fn) (φ : κ.c.F →+* K) (xg : Sp K ⟶ s.T.Z.X) (gf : EigFrame s.T.Z φ xg) (a : K), (∀ τ i, grNorm s.T.Z.t xg (latDR s.T.Z.t xg) (gf.v τ) i = 1) → IsCoord (Φ.C k) x gf (expo S.Dw (drSym la)) F a → drAt Φ k la p x F = ‖a‖ := by
  first | exact @GlobalTheory.CovHt.Link.DrAtFrame.drAt_eq_of_isCoord | exact GlobalTheory.CovHt.Link.DrAtFrame.drAt_eq_of_isCoord | (intros; apply GlobalTheory.CovHt.Link.DrAtFrame.drAt_eq_of_isCoord <;> assumption)
