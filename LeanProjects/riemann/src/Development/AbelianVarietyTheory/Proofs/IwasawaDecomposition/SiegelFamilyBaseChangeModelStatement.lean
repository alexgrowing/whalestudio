import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBaseChangeModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_base_change_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (κF : cycAway n →+* c.F) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (m0 : ObjMap o Xo.univ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → (∀ x, ((κF x : c.F) : ℂ) = (x : ℂ)) → ∃ (y : Xo.XF c ⟶ F.X) (α : o.t.G.left ⟶ F.univ.A.left) (α₂ : (G2 o.t.G).left ⟶ (G2 F.univ.A).left) (h : y ≫ F.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap κF), IsGrpPullback o.t.G F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ o.t.G o.t.PP.L) (F.univ.P.pull α₂) ∧ IsFinite (pullback.lift y _ h) := by
  first | exact @GlobalTheory.SiegelPoint.exists_finite_siegel_point | exact GlobalTheory.SiegelPoint.exists_finite_siegel_point | (intros; apply GlobalTheory.SiegelPoint.exists_finite_siegel_point <;> assumption)
