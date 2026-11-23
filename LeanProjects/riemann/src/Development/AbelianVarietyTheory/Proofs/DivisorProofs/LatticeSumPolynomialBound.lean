import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorusLatSum
open mixedEmbedding
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem exists_one_le_place (x : F) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ w : InfinitePlace F, 1 ≤ w x := by
  by_contra h
  push_neg at h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha : (⟨x, hx⟩ : 𝓞 F) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have := InfinitePlace.one_le_of_lt_one (w := w) ha (fun z _ => h z)
  exact absurd this (not_le.mpr (h w))

theorem place_natCast_mul (w : InfinitePlace F) (m : ℕ) (x : F) : w ((m : F) * x) = m * w x := by
  rw [← InfinitePlace.norm_embedding_eq, ← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul,
    Complex.norm_natCast]

theorem inv_le_sum_places (m : ℕ) (hm : 1 ≤ m) (x : F) (hint : IsIntegral ℤ ((m : F) * x)) (h0 : x ≠ 0) :
    (m : ℝ)⁻¹ ≤ ∑ w : InfinitePlace F, w x := by
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  obtain ⟨w, hw⟩ := exists_one_le_place _ hint (mul_ne_zero hm0 h0)
  rw [place_natCast_mul, mul_comm] at hw
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc (m : ℝ)⁻¹ ≤ w x := by rw [inv_le_iff_one_le_mul₀ hmpos]; exact hw
    _ ≤ _ := Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ w)

theorem norm_mixedEmbedding_le (x : F) : ‖(mixedEmbedding F x : NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ w : InfinitePlace F, w x := by
  have hs : 0 ≤ ∑ w : InfinitePlace F, w x := Finset.sum_nonneg fun w _ => apply_nonneg w x
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_) ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_)
  · rw [mixedEmbedding_apply_isReal, InfinitePlace.norm_embedding_of_isReal]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)
  · rw [mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)

theorem norm_pi_mixedEmbedding_le {κ : Type} [Fintype κ] (ξ : κ → F) :
    ‖((fun j => mixedEmbedding F (ξ j)) : κ → NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) := by
  have hs : 0 ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => (norm_mixedEmbedding_le (ξ j)).trans ?_
  exact Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
    (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) (Finset.mem_univ j)

theorem stepB (P P0 : ℝ) (hP0 : 0 < P0) (h : P0 ≤ P) (A N₀ D : ℕ) :
    P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ ≤ (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ := by
  have hP : 0 < P := hP0.trans_le h
  have e : P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ = (1 + P⁻¹) ^ N₀ * (P ^ D)⁻¹ := by
    have hP' : P ≠ 0 := hP.ne'
    rw [show (1 : ℝ) + P⁻¹ = (1 + P) * P⁻¹ by rw [add_mul, one_mul, mul_inv_cancel₀ hP', add_comm], mul_pow, pow_add, pow_add, inv_pow]
    field_simp
  rw [e]
  gcongr

theorem latG_tsum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  intro F _ _ κ _ _ q blk A N₀ c hc
  set L := GlobalTheory.LatScaleSum.latPi F κ with hL
  set D : ℕ := Module.finrank ℤ L + 1 with hD
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ D)⁻¹ with hH
  have hHs : Summable fun z : L => H z := GlobalTheory.LatScaleSum.summable_inv_one_add_pow F κ
  set P0 : ℝ := c ^ q with hP0def
  have hP0 : 0 < P0 := pow_pos hc q
  set B : ℝ := (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨A + N₀ + D, B * ∑' z : L, H z, q * (A + N₀ + D) + D, ?_⟩
  intro m t hm ht
  set N := A + N₀ + D with hN
  set P : ℝ := ∏ i, t i with hPdef
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (ht i)
  have hPP0 : P0 ≤ P := by
    rw [hP0def, hPdef]
    calc c ^ q = ∏ _i : Fin q, c := by simp
      _ ≤ ∏ i, t i := Finset.prod_le_prod (fun i _ => hc.le) (fun i _ => ht i)
  have hP : 0 < P := hP0.trans_le hPP0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have key : ∀ ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := by
    intro ξ
    have hR : 0 ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := mul_nonneg (by positivity) (hLnn _)
    unfold latG
    split_ifs with hblk
    swap
    · simpa using hR
    unfold majI
    split_ifs with hint
    swap
    · simpa using hR
    have hmem : g ξ ∈ L := GlobalTheory.LatScaleSum.mem_latPi F κ _ hint
    rw [hLind, Set.indicator_of_mem hmem]
    set S : Fin q → ℝ := fun i => ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j) with hS
    set s : ℝ := ∑ j, ∑ w : InfinitePlace F, w (ξ j) with hs
    have hS0 : ∀ i, (m : ℝ)⁻¹ ≤ S i := by
      intro i
      obtain ⟨j, hj, hξ⟩ := hblk i
      exact (inv_le_sum_places m hm (ξ j) (hint j) hξ).trans
        (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
          (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) hj)
    set Q : ℝ := ∏ i, (1 + t i * S i) with hQ
    have hQge : P * ((m : ℝ) ^ q)⁻¹ ≤ Q := by
      calc P * ((m : ℝ) ^ q)⁻¹ = ∏ i, (t i * (m : ℝ)⁻¹) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
        _ ≤ Q := Finset.prod_le_prod (fun i _ => by have := ht0 i; positivity) (fun i _ => by
              have := mul_le_mul_of_nonneg_left (hS0 i) (ht0 i).le
              exact le_add_of_nonneg_of_le zero_le_one this)
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
    have hQpos : 0 < P * ((m : ℝ) ^ q)⁻¹ := by positivity
    have hmaj : majW blk A N t ξ = P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ := by
      unfold majW
      rw [Finset.prod_pow]
    rw [hmaj]
    have hψn : ‖ψ ξ‖ ≤ s := norm_pi_mixedEmbedding_le ξ
    have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
    have hcc : ((1 + s) ^ N)⁻¹ ≤ (m : ℝ) ^ D * H (g ξ) := by
      have h1 : ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ (by linarith) (by omega)
      calc ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := h1
        _ ≤ ((1 + ‖ψ ξ‖) ^ D)⁻¹ := by gcongr
        _ = (m : ℝ) ^ D * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ D)⁻¹ := by
            rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
        _ ≤ (m : ℝ) ^ D * ((1 + ‖g ξ‖) ^ D)⁻¹ := by
            gcongr
            have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith [norm_nonneg (ψ ξ), hgn]
    have ha : (Q ^ N)⁻¹ ≤ (m : ℝ) ^ (q * N) * (P ^ N)⁻¹ := by
      calc (Q ^ N)⁻¹ ≤ ((P * ((m : ℝ) ^ q)⁻¹) ^ N)⁻¹ := by gcongr
        _ = _ := by rw [mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul, mul_comm]
    have hb := stepB P P0 hP0 hPP0 A N₀ D
    have hHg : 0 ≤ H (g ξ) := by positivity
    calc P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ * (1 + P) ^ N₀
        = P ^ A * (1 + P) ^ N₀ * (Q ^ N)⁻¹ * ((1 + s) ^ N)⁻¹ := by rw [mul_inv]; ring
      _ ≤ P ^ A * (1 + P) ^ N₀ * ((m : ℝ) ^ (q * N) * (P ^ N)⁻¹) * ((m : ℝ) ^ D * H (g ξ)) := by
          gcongr
      _ = (P ^ A * (1 + P) ^ N₀ * (P ^ N)⁻¹) * (m : ℝ) ^ (q * N + D) * H (g ξ) := by rw [pow_add]; ring
      _ ≤ B * (m : ℝ) ^ (q * N + D) * H (g ξ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) hHg
  have hnn : ∀ ξ, 0 ≤ latG (F := F) blk A N m t ξ := fun ξ => latG_nonneg blk A N m t ξ (fun i => (ht0 i).le)
  have hpow : 0 < (1 + P) ^ N₀ := by positivity
  have key' : ∀ ξ, latG (F := F) blk A N m t ξ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D)) * Lind (g ξ) := by
    intro ξ
    calc latG (F := F) blk A N m t ξ = ((1 + P) ^ N₀)⁻¹ * (latG (F := F) blk A N m t ξ * (1 + P) ^ N₀) := by
          field_simp
      _ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D) * Lind (g ξ)) := mul_le_mul_of_nonneg_left (key ξ) (by positivity)
      _ = _ := by ring
  have hu : Summable fun ξ => Lind (g ξ) := hLs.comp_injective hginj
  have hsum : Summable (latG (F := F) blk A N m t) := Summable.of_nonneg_of_le hnn key' (hu.mul_left _)
  refine ⟨hsum, ?_⟩
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  rw [← tsum_mul_right]
  calc ∑' ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ ∑' ξ, B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) :=
        (hsum.mul_right _).tsum_le_tsum key (hu.mul_left _)
    _ = B * (m : ℝ) ^ (q * N + D) * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ B * (m : ℝ) ^ (q * N + D) * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = B * (∑' z : L, H z) * (m : ℝ) ^ (q * N + D) := by ring

end GlobalTheory.ThKTorusLatSum
