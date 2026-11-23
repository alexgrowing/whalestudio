import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelRelDim

theorem relDim_and_isVB_omega : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo c Y
  have := Y.t.semi
  have hsm : Smooth Y.t.G.hom := Y.t.semi.smooth
  have : IsIso (spMap (RingHom.id c.F)) := by
    unfold spMap
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hdom : IsDominant (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hg : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom :=
    GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ Y.t.G.hom Y.oF.t.G.hom Y.m.φ _
      Y.m.cart.1 hdom hsm (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  exact ⟨hg, GlobalTheory.LieVB.isVB_omega Y.t.G _⟩

end GlobalTheory.ModelRelDim
