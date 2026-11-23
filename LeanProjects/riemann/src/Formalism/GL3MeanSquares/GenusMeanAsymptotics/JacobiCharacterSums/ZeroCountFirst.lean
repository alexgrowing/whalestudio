import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneSubTwoCpowLower
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneLeLogOfThreeLe

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem count_block0 (M : ℕ) (T σ c : ℝ) (S : Finset (DirichletCharacter ℂ 1 × ℂ)) (N U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 512 ≤ qd M T) (hc0 : 0 < c)
    (hc : 87880000 / c ^ 2 * Real.log (qd M T) ^ 7 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) N U (fun n => p.1 (n : ZMod 1)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (512 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le' (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le' (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := dyadic_index_le_log q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) + 1 := by positivity
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * q := by
    have : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * x := by
      rw [hx]; push_cast; nlinarith
    linarith
  have hθ : (0 : ℝ) < c / (((pJd M T : ℝ) + 1) * Real.log q) := by positivity
  have hsmall := first_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T)) ((pJd M T : ℝ) + 1) q (Real.sqrt q) (Real.log q) c
    (by linarith) (Real.sqrt_pos.2 (by linarith)) hc0 (rpow_neg_exponent_bound q U σ (by omega) hσ hU1)
    (by linarith) hl hK0 hK hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod 1)) (fun p => p.2) (pYd M T) N U σ
    (c / (((pJd M T : ℝ) + 1) * Real.log q)) (9 + 8 * Real.log (2 * T + 1))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound 1 S σ T U hU hT (by linarith) hS (fun p hp p' hp' hne _ => hsp p hp p' hp' hne))
    hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (c / (((pJd M T : ℝ) + 1) * Real.log q)) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * ((((pJd M T : ℝ) + 1) * Real.log q) ^ 2 / c ^ 2) := by
    have hLq0 : Real.log q ≠ 0 := by linarith
    field_simp
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  have hLq00 : 0 ≤ Real.log q := by linarith
  gcongr

theorem zero_count_first : Count0 := by
  obtain ⟨c, hc0, q₂, hdet⟩ := zero_detection_first
  obtain ⟨q₁, hq₁⟩ := log_pow_seven_le_sqrt (87880000 / c ^ 2)
  refine ⟨100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)), max (max q₁ q₂) 512, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq512 : 512 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq)
  have hq2 : q₂ ≤ qd M T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le' (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let e : DirichletCharacter ℂ M × ℂ → DirichletCharacter ℂ 1 × ℂ := fun p => (1, p.2)
  have hinj : Set.InjOn e (S : Set (DirichletCharacter ℂ M × ℂ)) := by
    intro p hp p' hp' h
    have h2 : (e p).2 = (e p').2 := congrArg Prod.snd h
    exact Prod.ext ((hS p hp).1.trans (hS p' hp').1.symm) h2
  set S' : Finset (DirichletCharacter ℂ 1 × ℂ) := S.image e with hS'
  have hcard : S'.card = S.card := card_image_of_injOn hinj
  let Sij : ℕ × ℕ → Finset (DirichletCharacter ℂ 1 × ℂ) := fun ij =>
    S'.filter (fun p => c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) (fun n => p.1 (n : ZMod 1)) p.2‖)
  have hsub : S' ⊆ (range 2 ×ˢ range (pJd M T + 1)).biUnion Sij := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS a ha
    rw [h1] at h5
    obtain ⟨i, hi, j, hj, hjb⟩ := hdet M T hT hM hq2 a.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨(i, j), mem_product.2 ⟨hi, hj⟩, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤ B := by
    intro ij hij
    have hjJ : ij.2 < pJd M T + 1 := mem_range.1 (mem_product.1 hij).2
    have hYN : 2 * (qd M T ^ 3 * 2 ^ pJd M T) ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve (qd M T) hq512
    apply count_block0 M T σ c (Sij ij) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) hM hT hσ hσ1 hq512
      hc0 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ ij.2) ≤ 2 * (qd M T ^ 3 * 2 ^ pJd M T) := by
            unfold pYd
            gcongr
            · norm_num
            · omega
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨-, h2, h3, h4, -⟩ := hS a ha
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp' hne
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨a', ha', rfl⟩ := mem_image.1 (mem_filter.1 hp').1
      exact hsp a ha a' ha' (fun h => hne (by rw [h]))
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    rw [hcard] at this
    exact_mod_cast this
  have h2 : ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤
      2 * ((pJd M T : ℝ) + 1) * B := by
    have := sum_le_card_nsmul (range 2 ×ˢ range (pJd M T + 1)) (fun ij => ((Sij ij).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log (qd M T) := dyadic_index_le_log (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (512 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq512
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : 2 * ((pJd M T : ℝ) + 1) * B ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := by gcongr
  have h4 : 2 * (50 * Real.log ((M : ℝ) * T)) * B =
      100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 9 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 9 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
