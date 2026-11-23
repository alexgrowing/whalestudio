import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPNFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusQuasiInverseScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TranslQuotientPow

theorem isMonHom_id_pow {Y : Scheme.{0}} (G : Over Y) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem comp_id_pow {Y : Scheme.{0}} {G W : Over Y} [GrpObj G] (x : W ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih, Category.comp_id]

theorem pow_comp_hom {Y : Scheme.{0}} {G A W : Over Y} [GrpObj G] [GrpObj A] (q : G ⟶ A) [IsMonHom q]
    (x : W ⟶ G) (n : ℕ) : (x ^ n) ≫ q = (x ≫ q) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_comp]
  | succ n ih => rw [pow_succ, pow_succ, mul_comp, ih]

end GlobalTheory.TranslQuotientPow
