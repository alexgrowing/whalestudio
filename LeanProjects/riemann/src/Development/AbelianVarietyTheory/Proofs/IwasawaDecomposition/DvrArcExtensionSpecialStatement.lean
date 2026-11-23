import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionSpecial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_arc_extension_special : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∀ (ϖ : T.V) (hϖ : Irreducible ϖ) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.ArcBuild.beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P), GlobalTheory.ArcBuild.TateCl P hϖ Y b y m hdiv hL := by
  first | exact @GlobalTheory.ArcBuildTate.tateCl | exact GlobalTheory.ArcBuildTate.tateCl | (intros; apply GlobalTheory.ArcBuildTate.tateCl <;> assumption)
