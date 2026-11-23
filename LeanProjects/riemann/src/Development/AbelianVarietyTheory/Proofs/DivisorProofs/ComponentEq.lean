import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformizaStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIsoStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open IsLocalRing

namespace GlobalTheory.NsmulPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem one_left (D : DegPre R) : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := by
  have e : (toUnit D.P.A).left = D.P.A.hom := by simpa using Over.w (toUnit D.P.A)
  show (toUnit D.P.A ≫ η[D.P.A]).left = _
  rw [Over.comp_left, e]
  rfl

theorem unit_left (D : DegPre R) : (toUnit D.P.A ≫ η[D.P.A]).left = D.P.A.hom ≫ eSec D.P.A := one_left D

theorem comp_padd (D : DegPre R) (a x : D.P.A ⟶ D.P.A) :
    a ≫ padd D.P.A (𝟙 D.P.A) x = padd D.P.A a (a ≫ x) := by
  simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]

theorem gen_shape (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k' k : ℕ) (hk : k ≤ k') (χ' χ : D.X)
    (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i))), eB.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val eB r z J = val κ r z J * rigV D (r ≫ D.P.A.hom) z J ^ ((k' : ℤ) - k) * val u r z J := by
  have hL := D.P.isLB
  let ρ := LB.pullGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ (GeneratorPullback.powGen D.P.L _ _ ρ (k' - k))) u
  have ht : t.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ (powGen_isGen _ _ _ _ hρ _)) hu
  have e₁ := comp_padd D a (toUnit D.P.A ≫ D.c χ)
  have e₂ : a ≫ toUnit D.P.A = toUnit D.P.A := toUnit_unique _ _
  have e₃ : a.left ≫ D.P.A.hom = D.P.A.hom := Over.w a
  obtain ⟨eB, he, hv⟩ := exists_gen hL (φ' := Sum.elim (D.famφB χ') (fun i => a.left ≫ D.famφB χ i))
    (ε' := Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Finset.univ_unique,
        Finset.prod_singleton, DegPre.famφB, DegPre.famε, DegPre.Oφ, Oε, Oinvε, kapLB, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Category.comp_id, ← Over.comp_left, e₁, ← Category.assoc, e₂, one_left, unit_left, Over.id_left, Nat.cast_sub hk, e₃, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, mul_one, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) t ht
  refine ⟨eB, he, fun Z r z J hJ => ?_⟩
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_pow, val_pull hJ, show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
  rfl

end GlobalTheory.NsmulPull

namespace GlobalTheory.NsmulPull

end GlobalTheory.NsmulPull

namespace GlobalTheory

end GlobalTheory
