import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_arc_extension_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∃ (T' : CDVR) (g : T.V →+* T'.V) (t : SAB H (Sp T'.V)) (_ : SABMap t Y.t (spMap g ≫ y)) (P : PELUnif (maximalIdeal T'.V) t), Function.Injective g ∧ IsLocalHom g ∧ P.TorsionIso := by
  first | exact @GlobalTheory.MemberUnif.exists_ext_unif_torsionIso | exact GlobalTheory.MemberUnif.exists_ext_unif_torsionIso | (intros; apply GlobalTheory.MemberUnif.exists_ext_unif_torsionIso <;> assumption)
