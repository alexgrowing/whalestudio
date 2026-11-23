import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNeg

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag

namespace GlobalTheory.WholeDual

theorem whole_inr_dual : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
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
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y C hm a R g p _
  refine ⟨fun k x => ?_, fun k v _ ε y => ?_⟩
  · refine GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.unitAt_genAt_mul _ _ ?_ x
    exact (congrArg (divOf Y) (GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.expo_single_neg_one _)).trans
      (GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.divOf_neg Y _)
  · exact GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one Y _ v ε y

end GlobalTheory.WholeDual
