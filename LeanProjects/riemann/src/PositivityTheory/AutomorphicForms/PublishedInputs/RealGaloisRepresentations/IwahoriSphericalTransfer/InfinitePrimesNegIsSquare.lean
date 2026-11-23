import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.PrimesNegSquare

open Polynomial

theorem isSquare_neg_of_dvd (q : ℕ) [Fact q.Prime] (p : ℕ) (h : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) :
    IsSquare (-(p : ℚ_[q])) := by
  obtain ⟨c, hc⟩ := h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have h2pos : 0 < ‖(2 : ℤ_[q])‖ := norm_pos_iff.mpr two_ne_zero
  have h2le : ‖(2 : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hcle : ‖((c : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hqn : ‖((q : ℕ) : ℤ_[q])‖ = (q : ℝ)⁻¹ := PadicInt.norm_p
  have key : ‖(((p : ℤ) + 1 : ℤ) : ℤ_[q])‖ < ‖(2 : ℤ_[q])‖ ^ 2 := by
    rw [hc]
    push_cast
    have e8 : (8 : ℤ_[q]) = 2 ^ 3 := by norm_num
    rw [e8, norm_mul, norm_mul, norm_pow, hqn]
    have hqinv : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have hqinv0 : 0 < (q : ℝ)⁻¹ := by positivity
    calc ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ * ‖((c : ℤ) : ℤ_[q])‖
        ≤ ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ := by
          apply mul_le_of_le_one_right (by positivity) hcle
      _ < ‖(2 : ℤ_[q])‖ ^ 2 * 1 := by
          rw [pow_succ, mul_assoc]
          apply mul_lt_mul_of_pos_left _ (by positivity)
          calc ‖(2 : ℤ_[q])‖ * (q : ℝ)⁻¹ ≤ 1 * (q : ℝ)⁻¹ := by gcongr
            _ < 1 := by simpa using hqinv
      _ = ‖(2 : ℤ_[q])‖ ^ 2 := mul_one _
  let F : ℤ[X] := X ^ 2 + C (p : ℤ)
  have hF : ‖aeval (1 : ℤ_[q]) F‖ < ‖aeval (1 : ℤ_[q]) (derivative F)‖ ^ 2 := by
    have e1 : aeval (1 : ℤ_[q]) F = (((p : ℤ) + 1 : ℤ) : ℤ_[q]) := by
      simp [F]; ring
    have e2 : aeval (1 : ℤ_[q]) (derivative F) = 2 := by
      simp [F]
      exact map_ofNat _ 2
    rw [e1, e2]; exact key
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  have hz' : z ^ 2 + (p : ℤ_[q]) = 0 := by simpa [F] using hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + (p : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at this
  linear_combination -this

theorem infinite_primes_neg_isSquare : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  intro q _
  have hq0 : (8 * q) ≠ 0 := by
    have := (Fact.out : q.Prime).pos; omega
  haveI : NeZero (8 * q) := ⟨hq0⟩
  have hu : IsUnit (-1 : ZMod (8 * q)) := isUnit_one.neg
  refine (Nat.infinite_setOfPred_prime_and_eq_mod hu).mono ?_
  rintro p ⟨hp, hpe⟩
  refine ⟨hp, GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_⟩
  have : (((p : ℤ) + 1 : ℤ) : ZMod (8 * q)) = 0 := by
    push_cast; rw [hpe]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

end GlobalTheory.RealGal.PrimesNegSquare
