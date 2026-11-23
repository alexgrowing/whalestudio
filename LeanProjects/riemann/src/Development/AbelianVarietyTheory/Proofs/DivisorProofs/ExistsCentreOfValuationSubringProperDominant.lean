import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProperCentre

theorem exists_regAt_centre : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  intro X Y _ _ s _ _ V x h
  let ψ : X.presheaf.stalk x →+* V :=
    ((GlobalTheory.functionFieldMap s).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      V.toSubring (fun a => h _ ⟨a, rfl⟩)
  let r : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hc : GlobalTheory.genericFieldPoint Y ≫ s = GlobalTheory.specAlgebraMap V Y.functionField ≫ r := by
    rw [← GlobalTheory.specMap_functionFieldMap, ← GlobalTheory.specAlgebraMap_fromSpecStalk x]
    simp only [r, GlobalTheory.specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc, ?_, ?_⟩
  · rw [GlobalTheory.apply_valCentre_base]
    have := (IsLocalRing.specializes_closedPoint (R := X.presheaf.stalk x)
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk x).continuous
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  · have hd : GlobalTheory.DominatesStalk V (GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc) :=
      GlobalTheory.dominatesStalk_iff_exists_hom.mpr
        ⟨_, GlobalTheory.specAlgebraMap_valExt s r (GlobalTheory.genericFieldPoint Y) hc, rfl⟩
    rintro f ⟨a, rfl⟩
    exact hd.1 a

end GlobalTheory.ProperCentre
