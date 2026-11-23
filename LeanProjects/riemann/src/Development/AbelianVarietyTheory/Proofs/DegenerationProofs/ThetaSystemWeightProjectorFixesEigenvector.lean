import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem proj_fixes_eigen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  intro o Ω _ _ _ S F _ y T c hT b E h
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, y (GlobalGen.chi S (c t)) * y S.ζN ^ (c t).val = 1 := fun t => by
    have h2 := GlobalGen.chi_add S (c t) (-(c t))
    rw [add_neg_cancel, GlobalGen.chi_zero] at h2
    rw [← map_pow, ← map_one y, h2, map_mul, GlobalGen.chi.eq_1 S (-(c t)), neg_neg]
  have h3 : y (Ring.inverse (Nat.card T : o)) * (Fintype.card T : F) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← map_natCast y, ← map_mul,
      Ring.inverse_mul_cancel _ (GlobalGen.isUnit_card hT), map_one]
  have h4 : ∑ i, b i * ∑ j, y (S.proj T c j i) * E j =
      y (Ring.inverse (Nat.card T : o)) * ∑ t : T, y (GlobalGen.chi S (c t)) *
        ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j := by
    simp only [GlobalGen.proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h4]
  simp only [h, ← _root_.mul_assoc, h1, _root_.one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← _root_.mul_assoc, h3, _root_.one_mul]

end GlobalTheory.TestFibre
