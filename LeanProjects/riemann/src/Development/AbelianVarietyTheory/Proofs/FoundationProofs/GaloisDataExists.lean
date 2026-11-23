import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaMemSum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GalExist

theorem exists_sum_of_mem_La (D : D7) (T : Tor D) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (y : VC D N N') (hy : y ∈ La D T L L') :
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Fin r → ℂ),
      (∀ j, b j ∈ YYl D L L') ∧ (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  first
  | exact @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | (apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum ..)

theorem galEx_of_galStar (D : D7) (hS : galStar D) : galEx D := by
  intro cc δ hc M ρ hK hD hM N N' L L' _ _ x n hx hn
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨r, b, w, hb, hw, hsum⟩ := exists_sum_of_mem_La D _ L L' _ hmx
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw' : ∀ j, w j ∈ lamOf D cc δ := hw
  have hmul : ∀ j, ((m * n : ℕ) : ℂ) * (w j / m / n) ∈ lamOf D cc δ := by
    intro j
    have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
    rw [this]; exact hw' j
  have hex : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
    intro j
    have hq : InRationalLattice (lamOf D cc δ) (w j / m / n) := ⟨m * n, Nat.mul_pos hm hn, hmul j⟩
    refine h1 _ hq ?_
    by_cases h : w j / m / n ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  choose t' ht' using hex
  refine ⟨∑ j, ((n : ℂ) * t' j) • embV D (torConj D (tor0 D cc δ) M ρ) (b j),
    ⟨r, b, fun j => w j / m, fun j => (n : ℂ) * t' j, hb, ?_, ?_, rfl, ?_⟩, m, hm, ?_⟩
  · intro j
    refine ⟨m, hm, ?_⟩
    have : (m : ℂ) * (w j / m) = w j := by field_simp
    rw [this]; exact hw j
  · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [hx, hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← div_eq_inv_mul]
  · intro j
    have : (n : ℂ) * t' j / n = t' j := by field_simp
    show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
    rw [this]; exact ht' j
  · rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    refine AddSubgroup.subset_closure ⟨((m * n : ℕ) : ℂ) * t' j, (h6 _ _ _ (ht' j)).1 (hmul j), b j, hb j, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast; ring

theorem galEx_all : ∀ D : D7, galEx D := fun D => galEx_of_galStar D (GlobalTheory.T.galStar_complexMultiplication_points D)

end GlobalTheory.GalExist
