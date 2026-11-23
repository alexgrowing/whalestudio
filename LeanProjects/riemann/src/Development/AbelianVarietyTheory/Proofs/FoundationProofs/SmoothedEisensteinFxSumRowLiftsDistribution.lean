import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisFDistribution
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw

noncomputable section

open Finset GlobalTheory.KummerEisensteinGalois
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.RowFibre

theorem val_lift (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n)) (s : ℕ) (hs : s < p) :
    ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))).val = x.val + p ^ n * s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply ZMod.val_cast_of_lt
  have hx := ZMod.val_lt x
  calc x.val + p ^ n * s < p ^ n + p ^ n * s := by omega
    _ = p ^ n * (s + 1) := by ring
    _ ≤ p ^ n * p := Nat.mul_le_mul_left _ hs
    _ = p ^ (n + 1) := by ring

theorem sum_lifts {α : Type*} [AddCommMonoid α] (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n))
    (f : ZMod (p ^ (n + 1)) → α) :
    ∑ y ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x)), f y
      = ∑ s ∈ range p, f ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpos : 0 < p ^ n := pow_pos hp.out.pos n
  have hmem : ∀ y : ZMod (p ^ (n + 1)),
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x ↔ y.val % p ^ n = x.val := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    constructor
    · rintro rfl; rw [ZMod.val_natCast]
    · intro h; rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]
  symm
  refine Finset.sum_nbij' (fun s => ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))))
    (fun y => y.val / p ^ n) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hs ⊢
    rw [hmem, val_lift p n x s hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  · intro y hy
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hy ⊢
    rw [Nat.div_lt_iff_lt_mul hpos]
    have := ZMod.val_lt y
    calc y.val < p ^ (n + 1) := this
      _ = p * p ^ n := by ring
  · intro s hs
    simp only [mem_coe, mem_range] at hs
    rw [val_lift p n x s hs, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (ZMod.val_lt x), zero_add]
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy
    rw [hmem] at hy
    rw [← hy, Nat.mod_add_div, ZMod.natCast_zmod_val]
  · intro s _
    rfl

theorem sum_range_perm {α : Type*} [AddCommMonoid α] (p : ℕ) [hp : Fact p.Prime] (H : ℤ → α)
    (hH : ∀ t, H t = H (t % p)) (c e : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ∑ s ∈ range p, H (c * ((s : ℤ) + e)) = ∑ k ∈ range p, H k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set Hz : ZMod p → α := fun z => H (z.val : ℤ) with hHz
  have hHt : ∀ t : ℤ, H t = Hz (t : ZMod p) := by
    intro t; rw [hH t, hHz]; simp only [ZMod.val_intCast]
  have hr : ∀ f : ZMod p → α, ∑ s ∈ range p, f (s : ZMod p) = ∑ z, f z := by
    intro f
    refine Finset.sum_nbij' (fun s => (s : ZMod p)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
    · intros; simp
    · intro z _; simp [ZMod.val_lt]
    · intro s hs
      simp only [mem_coe, mem_range] at hs
      simp [ZMod.val_cast_of_lt hs]
    · intro z _; simp
    · intros; rfl
  have hcz : (c : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hbij : Function.Bijective (fun z : ZMod p => (c : ZMod p) * (z + e)) := by
    rw [← Finite.injective_iff_bijective]
    intro a b h
    simpa using mul_left_cancel₀ hcz h
  calc ∑ s ∈ range p, H (c * ((s : ℤ) + e))
        = ∑ s ∈ range p, Hz ((c : ZMod p) * ((s : ZMod p) + e)) := by
        refine sum_congr rfl fun s _ => ?_
        rw [hHt]; push_cast; rfl
    _ = ∑ z, Hz ((c : ZMod p) * (z + e)) := hr (fun z => Hz ((c : ZMod p) * (z + e)))
    _ = ∑ z, Hz z := Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    _ = ∑ k ∈ range p, Hz (k : ZMod p) := (hr Hz).symm
    _ = ∑ k ∈ range p, H k := by
        refine sum_congr rfl fun k _ => ?_
        rw [hHt]; push_cast; rfl

theorem modEq_shift (p M : ℕ) (A t : ℤ) :
    A + (M : ℤ) * t ≡ A + (M : ℤ) * (t % p) [ZMOD ((p * M : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-(t / p), ?_⟩
  push_cast
  linear_combination (M : ℤ) * Int.emod_add_mul_ediv t p

theorem sum_perm2 {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime] (M j : ℕ) (hM : 0 < M)
    (ζ : K) (hζ : ζ ^ (p * M) = 1) (A₁ A₂ c e₁ e₂ : ℤ) (hc : ¬ (p : ℤ) ∣ c) (r : ℕ) :
    ∑ s₁ ∈ range p, ∑ s₂ ∈ range p,
        eisF j (p * M) ζ (A₁ + M * (c * ((s₁ : ℤ) + e₁))) (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * i₁) (A₂ + M * i₂) r := by
  have hL : 0 < p * M := Nat.mul_pos hp.out.pos hM
  have inner : ∀ a : ℤ, ∑ s₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * i₂) r := by
    intro a
    exact sum_range_perm p (fun t => eisF j (p * M) ζ a (A₂ + M * t) r)
      (fun t => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ (Int.ModEq.refl a)
        (modEq_shift p M A₂ t)) r) c e₂ hc
  simp only [inner]
  exact sum_range_perm p (fun t => ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * t) (A₂ + M * i₂) r)
    (fun t => sum_congr rfl fun i₂ _ => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ
      (modEq_shift p M A₁ t) (Int.ModEq.refl _)) r) c e₁ hc

theorem not_dvd_num (p : ℕ) [hp : Fact p.Prime] (N n : ℕ) (hn : 1 ≤ n) (hpN : ¬ p ∣ N) (x : ℕ)
    (hx : ¬ p ∣ x) (w c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * ((N : ℤ) * x + (p : ℤ) ^ n * w)) := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpn : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ (by omega)
  have h1 : (p : ℤ) ∣ ((N * p ^ n : ℕ) : ℤ) := by
    push_cast; exact Dvd.dvd.mul_left hpn _
  rcases hpz.dvd_or_dvd (h1.trans h) with h3 | h3
  · exact hc h3
  · have h4 : (p : ℤ) ∣ (N : ℤ) * x := (dvd_add_left (Dvd.dvd.mul_right hpn w)).mp h3
    rcases hpz.dvd_or_dvd h4 with h5 | h5
    · exact hpN (Int.natCast_dvd_natCast.mp h5)
    · exact hx (Int.natCast_dvd_natCast.mp h5)

theorem smF_sum_lifts : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K) (c : ℤ)
    (x₁ x₂ : ZMod (p ^ n)) (u₁ u₂ w₁ w₂ : ℤ), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ n →
    1 ≤ j → ¬ (p : ℤ) ∣ c → ¬ p ∣ x₁.val → (p : ℤ) * u₁ ≡ w₁ [ZMOD N] → (p : ℤ) * u₂ ≡ w₂ [ZMOD N] →
    ∀ r : ℕ, ∑ y₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₁)),
      ∑ y₂ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₂)),
      smF c j (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁.val : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * (y₂.val : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r =
      (p : K) ^ ((2 : ℤ) - (j : ℤ)) * vp p (smF c j (N * p ^ n) (ζ ^ p) ((N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁)
        ((N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂)) r := by
  intro p hp N n j K _ _ ζ c x₁ x₂ u₁ u₂ w₁ w₂ hζ hN hpN hn hj hc hx hu₁ hu₂ r
  have hpos : 0 < p := hp.out.pos
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hpos n)
  have hL : N * p ^ (n + 1) = p * (N * p ^ n) := by ring
  have hζ' : IsPrimitiveRoot ζ (p * (N * p ^ n)) := hL ▸ hζ
  have hζ1 : ζ ^ (p * (N * p ^ n)) = 1 := hζ'.pow_eq_one
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨k₁, hk₁⟩ := hu₁.dvd
  obtain ⟨k₂, hk₂⟩ := hu₂.dvd
  set A₁ : ℤ := (N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁ with hA₁
  set A₂ : ℤ := (N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂ with hA₂
  rw [hL, sum_lifts p n x₁]
  simp_rw [sum_lifts p n x₂]
  have key : ∀ s₁ ∈ range p, ∀ s₂ ∈ range p,
      smF c j (p * (N * p ^ n)) ζ
        ((N : ℤ) * ((((x₁.val + p ^ n * s₁ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * ((((x₂.val + p ^ n * s₂ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r
      = (c : K) ^ 2 * eisF j (p * (N * p ^ n)) ζ (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
            (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂))) r
        - (c : K) ^ ((2 : ℤ) - j) * eisF j (p * (N * p ^ n)) ζ (c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)))
            (c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂))) r := by
    intro s₁ hs₁ s₂ hs₂
    rw [mem_range] at hs₁ hs₂
    rw [val_lift p n x₁ s₁ hs₁, val_lift p n x₂ s₂ hs₂]
    have e₁ : (N : ℤ) * ((x₁.val + p ^ n * s₁ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁
        = A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)) := by
      rw [hA₁]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₁
    have e₂ : (N : ℤ) * ((x₂.val + p ^ n * s₂ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂
        = A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)) := by
      rw [hA₂]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₂
    have f₁ : c * (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
        = c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)) := by ring
    have f₂ : c * (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)))
        = c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂)) := by ring
    rw [e₁, e₂, smF, f₁, f₂]
  refine (sum_congr rfl fun s₁ hs₁ => sum_congr rfl fun s₂ hs₂ => key s₁ hs₁ s₂ hs₂).trans ?_
  simp only [sum_sub_distrib, ← mul_sum]
  have h1 : ¬ (p : ℤ) ∣ 1 := hpz.not_dvd_one
  have nd₁ : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ A₂) := fun h => by
    have := not_dvd_num p N n hn hpN x₁.val hx w₁ 1 h1
    rw [one_mul] at this
    exact this h.1
  have ndc : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ c * A₂) := fun h =>
    not_dvd_num p N n hn hpN x₁.val hx w₁ c hc h.1
  rw [sum_perm2 p (N * p ^ n) j hM ζ hζ1 A₁ A₂ 1 (-k₁) (-k₂) h1 r,
    sum_perm2 p (N * p ^ n) j hM ζ hζ1 (c * A₁) (c * A₂) c (-k₁) (-k₂) hc r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj A₁ A₂ nd₁ r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj (c * A₁) (c * A₂) ndc r]
  unfold vp smF
  split_ifs <;> ring

end GlobalTheory.KummerEisensteinGalois.RowFibre
