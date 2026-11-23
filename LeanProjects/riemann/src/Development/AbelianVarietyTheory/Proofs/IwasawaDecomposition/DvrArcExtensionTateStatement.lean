import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionTate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_arc_extension_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = zeta l.A → letI := H.starRing; ∃ J : TateIso D F (Out.TFK (R := T.V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a) (fun n g g' c => Out.WeilIs P.A.A P.A.L n g g' (unitOn c)), (J.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) ∧ (∀ a q, QkExt (algebraMap _ F) (hL.1 a).choose q → P.ToA F l.A q (J.ev l.A a)) ∧ ∀ a (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)), ∀ q, QkExt (algebraMap _ F) (hL.2 a ha).choose q → P.ToA F l.M q (J.ev l.M a) := by
  first | exact @GlobalTheory.TateGeneric.exists_tateIso_generic | exact GlobalTheory.TateGeneric.exists_tateIso_generic | (intros; apply GlobalTheory.TateGeneric.exists_tateIso_generic <;> assumption)
