import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddiStatement

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

noncomputable section

namespace GlobalTheory.LatValSum

theorem norm_le_one_of_isIntegral_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one {q : ℕ} [Fact q.Prime] {n : ℕ} (hn : n.Coprime q) : ‖(n : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q]) := (map_natCast _ n).symm
  rw [e]
  have h : ‖algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q])‖ = ‖((n : ℕ) : ℚ_[q])‖ := PadicComplex.norm_extends' (p := q) _
  rw [h]
  exact Padic.norm_natCast_eq_one_iff.mpr hn.symm

local notation "K" => algebraicClosure ℚ ℂ

theorem valGe_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) →
    (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  intro l hl r J _ u x hu hx
  haveI : Fact l.Prime := ⟨hl⟩
  have hx' := fun j => (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r (x j ^ 12)).1 (hx j)
  refine (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r _).2 ?_
  intro lam

  have huK : ∀ j, ∃ h : u j ∈ K, ‖lam ⟨u j, h⟩‖ ≤ 1 := by
    intro j
    obtain ⟨n, hn, hint⟩ := hu j
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by
        rintro rfl
        exact hl.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)
      exact_mod_cast this
    have hmK : (n : ℂ) * u j ∈ K :=
      mem_algebraicClosure_iff.mpr (hint.tower_top (A := ℚ)).isAlgebraic
    have hnK : (n : ℂ) ∈ K := IntermediateField.natCast_mem (algebraicClosure ℚ ℂ) n
    have huj : u j = ((n : ℂ) * u j) * (n : ℂ)⁻¹ := by field_simp
    have hK : u j ∈ K := by rw [huj]; exact (algebraicClosure ℚ ℂ).mul_mem hmK ((algebraicClosure ℚ ℂ).inv_mem hnK)
    refine ⟨hK, ?_⟩
    have he : (⟨(n : ℂ) * u j, hmK⟩ : K) = (n : K) * ⟨u j, hK⟩ := Subtype.ext (by simp)
    have hI : IsIntegral ℤ (lam ⟨(n : ℂ) * u j, hmK⟩) := by
      have h2 : IsIntegral ℤ (⟨(n : ℂ) * u j, hmK⟩ : K) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K ℂ) Subtype.val_injective).mp hint
      convert map_isIntegral_int lam h2
      exact Subsingleton.elim _ _
    have h1 := norm_le_one_of_isIntegral_int hI
    rw [he, map_mul, map_natCast, norm_mul, norm_natCast_eq_one hn, one_mul] at h1
    exact h1

  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hpow : ((l : ℝ) ^ (r / 12)) ^ (12 : ℕ) = (l : ℝ) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hxK : ∀ j, ∃ h : x j ∈ K, ‖lam ⟨x j, h⟩‖ ≤ (l : ℝ) ^ (r / 12) := by
    intro j
    obtain ⟨h12, hb⟩ := hx' j lam
    have hK : x j ∈ K := mem_algebraicClosure_iff.mpr
      ((mem_algebraicClosure_iff.mp h12).of_pow (by norm_num))
    refine ⟨hK, ?_⟩
    have he : (⟨x j ^ 12, h12⟩ : K) = (⟨x j, hK⟩ : K) ^ 12 := Subtype.ext (by simp)
    rw [he, map_pow, norm_pow, ← hpow] at hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hb
  choose hu1 hu2 using huK
  choose hx1 hx2 using hxK
  have hSK : (∑ j, u j * x j) ∈ K := (algebraicClosure ℚ ℂ).sum_mem fun j _ => (algebraicClosure ℚ ℂ).mul_mem (hu1 j) (hx1 j)
  have hS12 : (∑ j, u j * x j) ^ 12 ∈ K := (algebraicClosure ℚ ℂ).pow_mem hSK 12
  refine ⟨hS12, ?_⟩
  have he : (⟨(∑ j, u j * x j) ^ 12, hS12⟩ : K) = (∑ j, (⟨u j, hu1 j⟩ : K) * ⟨x j, hx1 j⟩) ^ 12 :=
    Subtype.ext (by simp)
  rw [he, map_pow, norm_pow, ← hpow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 12
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [map_mul, norm_mul]
  calc ‖lam ⟨u j, hu1 j⟩‖ * ‖lam ⟨x j, hx1 j⟩‖ ≤ 1 * (l : ℝ) ^ (r / 12) :=
        mul_le_mul (hu2 j) (hx2 j) (norm_nonneg _) zero_le_one
    _ = (l : ℝ) ^ (r / 12) := one_mul _

end GlobalTheory.LatValSum
