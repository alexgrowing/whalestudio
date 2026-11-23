import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFibreOpenEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_fibre_open_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (Z : ∀ c : Coeff l, Model Xo c (algebraMap (𝓞 c.F) c.F)) (BD : ∀ c, EffCartierData (Z c).X) (φ : InvFun (𝓞 E)) (m : ℕ), PolMapSt → IsTwInv H φ → (∀ c, IsPol φ m (Z c) (BD c)) → ∀ c : Coeff l, ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (jK : Xo.X ⟶ XK) (e : pullback (Z c).s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ XK), IsOpenImmersion jK ∧ jK ≫ sK = Xo.s ∧ IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ (Z c).jQ ≫ e = pullback.fst _ _ ≫ jK ∧ ∀ (T : Scheme.{0}) [T.IsSeparated] (g : pullback (Z c).s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ T) (g₀ : Xo.X ⟶ T), (Z c).jQ ≫ g = pullback.fst _ _ ≫ g₀ → ∃ h : XK ⟶ T, e ≫ h = g ∧ jK ≫ h = g₀ := by
  first | exact @GlobalTheory.GenericDescent.exists_generic_descent | exact GlobalTheory.GenericDescent.exists_generic_descent | (intros; apply GlobalTheory.GenericDescent.exists_generic_descent <;> assumption)
