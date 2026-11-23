import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelPullbackDvrExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_pullback_dvr_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g n : ℕ) (R : Type) [CommRing R] (ω : R →+* c.F) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), IsDedFrac ω → IsSiegPull s j G e κ C π → ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (χ : Sp W ⟶ C.X) (t : SAB H (Sp W)) (_ : SABMap t C.t χ) (P : PELUnif I t), Set.range (jK W ≫ χ) ⊆ Set.range C.j → ∃ π' : t.G.left ⟶ G.left, IsUnifOf F j e (χ ≫ π) π' P.U := by
  first | exact @GlobalTheory.SiegLoc.PelUnif.isUnifOf_pel | exact GlobalTheory.SiegLoc.PelUnif.isUnifOf_pel | (intros; apply GlobalTheory.SiegLoc.PelUnif.isUnifOf_pel <;> assumption)
