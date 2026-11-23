import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreserved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_span_preserved : ∀ (S : Type) [CommRing S] (m a k b : ℕ) (Q : Type) [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S), a ≤ k → k ≤ b → (LinearIndependent S c → LinearIndependent S (gvec c w x)) ∧ Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) ∧ ∀ e : ℕ, e ≤ a ∨ b ≤ e → initSpan S (gvec c w x) e = initSpan S c e := by
  first | exact @GlobalTheory.GrCl.gvec_frame | exact GlobalTheory.GrCl.gvec_frame | (intros; apply GlobalTheory.GrCl.gvec_frame <;> assumption)
