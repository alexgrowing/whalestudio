import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairOfC
import GroundTheory.Brauer.SkolemNoether
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorsNonzeroTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKIrr
variable {p : ℕ} [Fact p.Prime]

theorem irreducible_minpoly_inv (G : HTGroup p) (γ : G.Cˣ) (hirr : Irreducible (minpoly G.F (γ : G.C))) :
    Irreducible (minpoly G.F ((γ⁻¹ : G.Cˣ) : G.C)) := by
  have hi : IsIntegral G.F (γ : G.C) := Algebra.IsIntegral.isIntegral _
  set m := minpoly G.F (γ : G.C) with hmdef
  haveI : Fact (Irreducible m) := ⟨hirr⟩
  have hm0 : m ≠ 0 := minpoly.ne_zero hi
  haveI : FiniteDimensional G.F (AdjoinRoot m) := (AdjoinRoot.powerBasis hm0).finite
  have hz : ∀ a : Polynomial G.F, a ∈ Ideal.span {m} → Polynomial.aeval (γ : G.C) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, minpoly.aeval, zero_mul]
  let f : AdjoinRoot m →ₐ[G.F] G.C := Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
  have ef : f (AdjoinRoot.root m) = γ := by
    show Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
      (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aeval_X _
  have hinj : Function.Injective f := f.toRingHom.injective
  have hr0 : AdjoinRoot.root m ≠ 0 := by
    intro h
    have : (γ : G.C) = 0 := by rw [← ef, h, map_zero]
    exact γ.ne_zero this
  have hinv : f ((AdjoinRoot.root m)⁻¹) = ((γ⁻¹ : G.Cˣ) : G.C) := by
    have h1 : f ((AdjoinRoot.root m)⁻¹) * γ = 1 := by
      rw [← ef, ← map_mul, inv_mul_cancel₀ hr0, map_one]
    calc f ((AdjoinRoot.root m)⁻¹) = f ((AdjoinRoot.root m)⁻¹) * γ * ((γ⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  rw [← hinv, minpoly.algHom_eq f hinj]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open Polynomial GlobalTheory.GlobEig

theorem exists_emb_isRoot_irr {F C E : Type} [Field F] [NumberField F] [Ring C] [Algebra F C]
    [Algebra ℚ C] [IsScalarTower ℚ F C] [FiniteDimensional F C] [Field E] [Algebra ℚ E] [IsAlgClosed E]
    (y : C) (hirr : Irreducible (minpoly F y)) (μ : E) (h : ((minpoly ℚ y).map (algebraMap ℚ E)).IsRoot μ) :
    ∃ τ : F →+* E, ((minpoly F y).map τ).IsRoot μ := by
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  haveI : FiniteDimensional F (AdjoinRoot (minpoly F y)) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hyi)).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly F y)) := Module.Finite.trans F _
  haveI : Algebra.IsAlgebraic ℚ (AdjoinRoot (minpoly F y)) := Algebra.IsAlgebraic.of_finite ℚ _
  set r := AdjoinRoot.root (minpoly F y)
  have hdvd : minpoly ℚ y ∣ minpoly ℚ r := by
    apply minpoly.dvd
    have h1 : minpoly F y ∣ (minpoly ℚ r).map (algebraMap ℚ F) := by
      rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨k, hk⟩ := h1
    rw [← aeval_map_algebraMap F, hk, map_mul, minpoly.aeval, zero_mul]
  have hne : minpoly ℚ r ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral r)
  have hμ' : μ ∈ (minpoly ℚ r).rootSet E := by
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, map_mul, aeval_def, eval₂_eq_eval_map, h.eq_zero, zero_mul]
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hμ'
  obtain ⟨ψ, hψ⟩ := hμ'
  refine ⟨(ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _), ?_⟩
  rw [← hψ, IsRoot.def, eval_map]
  change eval₂ ((ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _))
    ((ψ : AdjoinRoot (minpoly F y) →+* E) r) (minpoly F y) = 0
  rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem root_norm_le_irr {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β y : G.Cˣ) (c : ℚˣ)
    (hirr : Irreducible (minpoly G.F (y : G.C)))
    (hyc : (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β) (B : ℝ) (hc : ‖((c : ℚ) : ℚ_[p])‖ ≤ B)
    (hc' : ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B)
    (hy : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (hyi : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (μ : PadicAlgCl p) (hμ : ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ) :
    ‖μ‖ ≤ B * B := by
  have h0 := isRoot_minpoly_of_isRoot_charpoly (y : G.C) μ hμ
  obtain ⟨τ, hτ⟩ := exists_emb_isRoot_irr (F := G.F) (y : G.C) hirr μ h0
  have hcpos : 0 < ‖((c : ℚ) : ℚ_[p])‖ := norm_pos_iff.2 (by simp)
  have hprod : ‖((c : ℚ) : ℚ_[p])‖ * ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, ← Rat.cast_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Rat.cast_one, norm_one]
  have hB0 : 0 ≤ B := hcpos.le.trans hc
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ B * B := by
      rw [← hprod]
      exact mul_le_mul hc hc' (norm_nonneg _) hB0
    nlinarith
  rcases liesOver_or_conj G τ with hu | hu
  · obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G τ hu y μ hτ
    have h1 := hy i ν hν
    rw [hνμ] at h1
    nlinarith
  · have h2 := isRoot_minpoly_sh G y τ μ hτ
    obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G _ hu (sh G y) μ h2
    have h3 := isRoot_inv G i β y c hyc ν hν
    have h4 := hyi i _ h3
    have hs : ‖((c : ℚ) : PadicAlgCl p)‖ = ‖((c : ℚ) : ℚ_[p])‖ := by
      rw [← PadicAlgCl.norm_extends, map_ratCast]
    rw [norm_mul, norm_inv, hs, hνμ, ← div_eq_mul_inv, div_le_iff₀ hcpos] at h4
    calc ‖μ‖ ≤ B * ‖((c : ℚ) : ℚ_[p])‖ := h4
      _ ≤ B * B := mul_le_mul_of_nonneg_left hc hB0

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open GlobalTheory.LKMid.Northcott

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr
