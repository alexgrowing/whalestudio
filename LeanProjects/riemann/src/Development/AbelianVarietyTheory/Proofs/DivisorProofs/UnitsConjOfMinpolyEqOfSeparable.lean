import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem conj_rel_alg' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β e e' : G.Cˣ) (a' : G.C) (r r' : ℚˣ) :
    algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) =
      algebraMap ℚ G.C ((r : ℚ) / r') * (((e * e'⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (r' : ℚ) *
        ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))) *
        ((β : G.C) * sh G ((e * e'⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  have hsh : sh G ((e * e'⁻¹ : G.Cˣ) : G.C) = sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C) := by
    simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : sh G (e' : G.C) * sh G ((e'⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hrr : (r' : ℚ) * ((r : ℚ) / r') = r := by field_simp
  have key2 : ((e : G.C) * ((e'⁻¹ : G.Cˣ) : G.C)) * ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) *
      ((β : G.C) * (sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C)) * ((β⁻¹ : G.Cˣ) : G.C)) =
      (e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left, ← mul_assoc (sh G (e' : G.C)), h1, one_mul]
  rw [hsh, Units.val_mul]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, hrr]
  rw [key2]

theorem commute_of_commute_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (y₀ : G.C)
    (hsep : (minpoly G.F y₀).Separable) (hdeg : (minpoly G.F y₀).natDegree = G.n) (a b : G.C)
    (ha : Commute a y₀) (hb : Commute b y₀) : Commute a b := by
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hamem : a ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact ha.eq.symm
  have hbmem : b ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hb.eq.symm
  rw [hc] at hamem
  have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({y₀} : Set G.C) hamem
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 b hbmem).symm

theorem units_conj_of_minpoly_eq_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ)
    (hab : minpoly G.F (a : G.C) = minpoly G.F (b : G.C)) (hsep : (minpoly G.F (b : G.C)).Separable)
    (hdeg : (minpoly G.F (b : G.C)).natDegree = G.n) : ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  haveI : Infinite G.F := Infinite.of_injective (Nat.cast : ℕ → G.F) Nat.cast_injective
  obtain ⟨g, hg⟩ := GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq G.F G.C G.n G.rankC (b : G.C) (a : G.C) hsep hdeg hab
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.LKCx.ClsReg
