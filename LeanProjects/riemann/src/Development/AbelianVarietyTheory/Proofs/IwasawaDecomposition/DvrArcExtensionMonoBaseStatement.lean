import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_arc_extension_mono_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Mono (spMap β) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∃ (T' : CDVR) (g : T.V →+* T'.V) (ϖ : T'.V) (io' : c.F →+* T'.Fr) (z' : Sp T'.Fr ⟶ Xo.XF c) (t' : SAB H (Sp T'.V)) (m' : SABMap t' Y.t (spMap g ≫ y)) (P' : PELUnif (maximalIdeal T'.V) t'), Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧ (algebraMap T'.V T'.Fr).comp (g.comp b) = io'.comp β ∧ z' ≫ pullback.snd _ _ = spMap io' ∧ z' ≫ Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap g ≫ y ∧ P'.TorsionIso ∧ (∀ Q : P'.D.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ P'.D.toPre ϖ Q → ∀ u v, (2 * l.M' : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf P'.D.toPre Q u v) ∧ GlobalTheory.ArcExt.LevelReps Y (spMap g ≫ y) t' m' P' := by
  first | exact @GlobalTheory.ArcExt.exists_ext_levelReps | exact GlobalTheory.ArcExt.exists_ext_levelReps | (intros; apply GlobalTheory.ArcExt.exists_ext_levelReps <;> assumption)
