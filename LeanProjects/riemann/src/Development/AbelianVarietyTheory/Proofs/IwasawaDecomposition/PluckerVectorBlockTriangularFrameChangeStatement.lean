import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluckerVector_blockTriangular_frame_change : ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (c c' : Let m → Fin (M + 1) → S) (d : Let m → S) (k : ℕ) (e : Fin k → Let m), Tri c c' d → Down e → plk c' e = (∏ l, d (e l)) • plk c e := by
  first | exact @GlobalTheory.FlagEmb.plk_tri | exact GlobalTheory.FlagEmb.plk_tri | (intros; apply GlobalTheory.FlagEmb.plk_tri <;> assumption)
