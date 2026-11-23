import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenEmbeddingOfLevelOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_embedding_of_level_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (s : Sys Xo) (l : Level H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (c : Coeff l) (Z : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), l.A = 1 → DomAll s hg Z → (∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (jK : (Xo l).X ⟶ XK) (e : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ XK), IsOpenImmersion jK ∧ jK ≫ sK = (Xo l).s ∧ IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ Z.jQ ≫ e = pullback.fst _ _ ≫ jK ∧ ∀ (T : Scheme.{0}) [T.IsSeparated] (g : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ T) (g₀ : (Xo l).X ⟶ T), Z.jQ ≫ g = pullback.fst _ _ ≫ g₀ → ∃ h : XK ⟶ T, e ≫ h = g ∧ jK ≫ h = g₀) → Z.Descends := by
  first | exact @GlobalTheory.DomGrpDescent.descends_of_dominates_of_generic | exact GlobalTheory.DomGrpDescent.descends_of_dominates_of_generic | (intros; apply GlobalTheory.DomGrpDescent.descends_of_dominates_of_generic <;> assumption)
