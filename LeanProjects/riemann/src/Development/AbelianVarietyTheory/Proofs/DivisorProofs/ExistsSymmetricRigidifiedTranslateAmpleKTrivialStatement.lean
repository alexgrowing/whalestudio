import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  first | exact @GlobalTheory.SymTranslate.exists_sym_translate | exact GlobalTheory.SymTranslate.exists_sym_translate | (intros; apply GlobalTheory.SymTranslate.exists_sym_translate <;> assumption)
