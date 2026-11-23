import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  first | exact @GlobalTheory.EtaVal.datAt_of_uniformisation | exact GlobalTheory.EtaVal.datAt_of_uniformisation | (intros; apply GlobalTheory.EtaVal.datAt_of_uniformisation <;> assumption)
