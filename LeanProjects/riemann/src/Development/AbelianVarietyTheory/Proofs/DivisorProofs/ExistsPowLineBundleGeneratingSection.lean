import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticZeroDimensionalFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealInverseBoundedIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupTorsionPrincipalPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsZeroDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPrincipalDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAddDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorEqOfSectionsEqStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

open GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.PicOrderTors

theorem gen_pow : ∀ (k : Type) [CommRing k] (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'],
    IsArithVar (spMap (algebraMap k k')) 0 → ∀ (B : LB (Sp k')), B.IsLB →
      ∃ e : ℕ, 0 < e ∧ ∃ t : LB.Gen (lbPow B e), t.IsGen := by
  intro k _ k' _ _ _ h B hB
  haveI : IsIntegral (Sp k') := h.isIntegral
  haveI : IsFractionRing Γ(Sp k', ⊤) (Sp k').functionField :=
    functionField_isFractionRing_of_isAffineOpen _ ⊤ (isAffineOpen_top _)
  haveI : CharZero Γ(Sp k', ⊤) := h.charZero
  haveI : Module.Finite ℤ k' := GlobalTheory.T.arithmetic_zero_dimensional_finite k k' h
  haveI : Module.Finite ℤ Γ(Sp k', ⊤) := Module.Finite.equiv
    (Scheme.ΓSpecIso (CommRingCat.of k')).commRingCatIsoToRingEquiv.symm.toAddEquiv.toIntLinearEquiv
  obtain ⟨M, hM, happ⟩ := GlobalTheory.T.fractional_ideal_inverse_bounded_index Γ(Sp k', ⊤) (Sp k').functionField
  obtain ⟨D, hD⟩ := Cartier.toPic_surjective (cls B hB)
  have hIJ : D.sections * (-D).sections = 1 := by
    rw [← GlobalTheory.T.sections_add_divisor, add_neg_cancel, GlobalTheory.T.sections_zero_divisor]
  obtain ⟨e, he, x, hx⟩ := GlobalTheory.T.class_group_torsion_principal_power _ _ M hM happ _ _ hIJ
  have hpow : ∀ n : ℕ, (n • D).sections = D.sections ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero, GlobalTheory.T.sections_zero_divisor]
    | succ n ih => rw [succ_nsmul, GlobalTheory.T.sections_add_divisor, ih, pow_succ]
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : D.sections ^ e * (-D).sections ^ e = 1 := by rw [← mul_pow, hIJ, one_pow]
    rw [hx, Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at h1
    have h2 : (1 : (Sp k').functionField) ∈ (1 : Submodule Γ(Sp k', ⊤) (Sp k').functionField) :=
      Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [← h1, Submodule.mem_bot] at h2
    exact one_ne_zero h2
  have hg : e • D = principal (Units.mk0 x hx0)⁻¹ :=
    GlobalTheory.T.divisor_eq_of_sections_eq _ _ _ (by rw [hpow, hx, GlobalTheory.T.sections_principal_divisor]; simp)
  have hL : (lbPow B e).IsLB := isLB_lbPow hB e
  refine ⟨e, he, (cls_eq_zero_iff hL).1 ?_⟩
  rw [cls_lbPow hB e hL, ← hD, ← map_nsmul, hg, toPic_principal]

end GlobalTheory.PicOrderTors
