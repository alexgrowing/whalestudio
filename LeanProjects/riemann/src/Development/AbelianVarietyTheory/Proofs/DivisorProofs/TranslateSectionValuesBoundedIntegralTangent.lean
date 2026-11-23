import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trVal_bounded : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν k hk s gm₀ gm _ hpull α
  obtain ⟨S, hS, hint⟩ := hν
  obtain ⟨n, a, σ, σF, hsc, hsum⟩ := GlobalTheory.T.familySection_span_pullbacks_unitBall V D C hC S hS k hk (ν.eX α) (s.s (ν.eX α))
  refine ⟨∑ i, ‖a i‖, fun mu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint V D.toPre C gm₀ gm hpull (ν.eX mu)
  have e := GlobalTheory.T.dualNumberSectionValue_linearCombination V D.toPre C k (ν.eX α) (s.s (ν.eX α)) n a σF hsum _ ν.J ν.good h3
  have hb := fun i => GlobalTheory.T.pulledBackSection_integralValue_dualPoint V D C hC N ν ⟨S, hS, hint⟩ k _ (σ i) (σF i) (hsc i) _ h2 _ h1
  have hv : trVal ν s gm α mu = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i)
      ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫
        (DegPre.trF D.toPre C (ν.eX mu)).left) ν.J := e
  rw [hv]
  constructor
  · rw [TrivSqZeroExt.fst_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).1
  · rw [TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).2

end GlobalTheory.MBLow

end
