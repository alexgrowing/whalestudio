import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationAdelicUnitHeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_compactification_adelic_unit_height : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : GlobalTheory.ShFam.FlagCpt Z e) {C : CxSt F} (hm : Mets Y C)
    (a : ℕ → Bool) (R : Option ℝ) (g : ℕ) (p : ℕ), p.Prime →
    (∀ (k : Fin g) x, UnitAt x (genAt (adlOf Y hm (wholeSym a R (Sum.inr k : Fin g ⊕ Fin g))).D x *
      genAt (adlOf Y hm (wholeSym a R (Sum.inl (Fin.rev k) : Fin g ⊕ Fin g))).D x)) ∧
    ∀ (k : Fin g) v, resP v = p → ∀ (ε : Ext v) (y : AlgPt Y.Y),
      (adlOf Y hm (wholeSym a R (Sum.inr k : Fin g ⊕ Fin g))).lg v ε y =
        -(adlOf Y hm (wholeSym a R (Sum.inl (Fin.rev k) : Fin g ⊕ Fin g))).lg v ε y +
        Real.log (ε.w (GlobalTheory.TrueGeo.valAt y.1 (genAt (adlOf Y hm (wholeSym a R (Sum.inr k : Fin g ⊕ Fin g))).D (below y.1) *
          genAt (adlOf Y hm (wholeSym a R (Sum.inl (Fin.rev k) : Fin g ⊕ Fin g))).D (below y.1)))) := by
  first | exact @GlobalTheory.WholeDual.whole_inr_dual | exact GlobalTheory.WholeDual.whole_inr_dual | (intros; apply GlobalTheory.WholeDual.whole_inr_dual <;> assumption)
