import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixGamSub
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.TateInv

theorem sub_one_mul_sum {R : Type*} [CommRing R] (ω : R) (n : ℕ) :
    (ω - 1) * ∑ s ∈ Finset.range n, (s : R) * ω ^ s = n * ω ^ n - ω * ∑ s ∈ Finset.range n, ω ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sub_one_mul_sum_eq {Ω : Type*} [Field Ω] (ω : Ω) (p : ℕ) (h1 : ω ≠ 1) (hp : ω ^ p = 1) :
    (ω - 1) * ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s = p := by
  rw [sub_one_mul_sum, hp, geom_sum_eq h1, hp, sub_self, zero_div, mul_zero, sub_zero, mul_one]

theorem pow_apply_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t i : ℕ) : (γ ^ t) (ζ ^ i) = ζ ^ (i * a ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, pow_succ]
    congr 1; ring

theorem pow_apply_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t : ℕ) {x : Ω} (hx : x ∈ Subring.closure {ζ}) : (γ ^ t) x ∈ Subring.closure {ζ} := by
  have h : Subring.closure {ζ} ≤ (Subring.closure {ζ}).comap ((γ ^ t : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω) := by
    rw [Subring.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Subring.mem_comap]
    have := pow_apply_pow γ ζ a hγ t 1
    simp only [pow_one, one_mul] at this
    show (γ ^ t) ζ ∈ _
    rw [this]
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  exact h hx

theorem mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m)) (i : ℕ)
    (hi : ¬ p ^ (L - m) ∣ i) :
    ∃ H ∈ Subring.closure {ζ}, (p : Ω) * ζ ^ i = γ H - H := by
  have hp : p.Prime := hpf.out
  obtain ⟨hmL, K, d, u, hd, hu, he, -⟩ := GlobalTheory.K5.MonX.exists_pow_eq hp2 hm1 hi
  have hpL : p ^ L = p ^ (L - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  set ω := ζ ^ (u * d * p ^ (L - 1)) with hω
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, hpL]
    intro h
    have h' : p ^ (L - 1) * p ∣ p ^ (L - 1) * (u * d) := by rwa [mul_comm (p ^ (L - 1)) (u * d)]
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h'
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact hu h
    · exact hd h
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨u * d, by rw [hpL]; ring⟩
  have hγω : γ ω = ω := by
    rw [hω, map_pow, hγ, ← pow_mul]
    have e : (1 + p ^ m) * (u * d * p ^ (L - 1)) = u * d * p ^ (L - 1) + p ^ L * (u * d * p ^ (m - 1)) := by
      rw [hpL, hpm]; ring
    rw [e, pow_add, pow_mul ζ (p ^ L), hζ.pow_eq_one, one_pow, mul_one]
  have hγtω : ∀ t : ℕ, (γ ^ t) ω = ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hγω]
  set S : Ω := ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s with hS
  have hγtS : ∀ t : ℕ, (γ ^ t) S = S := by
    intro t
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, map_natCast, map_pow, hγtω]
  have hK : (γ ^ K) (ζ ^ i) = ω * ζ ^ i := by
    rw [pow_apply_pow γ ζ _ hγ, he, pow_add, hω, mul_comm]
  have hωmem : ω ∈ Subring.closure {ζ} := Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  have hSmem : S ∈ Subring.closure {ζ} :=
    Subring.sum_mem _ fun s _ => Subring.mul_mem _ (natCast_mem _ s) (Subring.pow_mem _ hωmem _)
  have hH0 : S * ζ ^ i ∈ Subring.closure {ζ} :=
    Subring.mul_mem _ hSmem (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _)
  refine ⟨∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i),
    Subring.sum_mem _ fun t _ => pow_apply_mem γ ζ _ hγ t hH0, ?_⟩
  have hγH : γ (∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i)) = ∑ t ∈ Finset.range K, (γ ^ (t + 1)) (S * ζ ^ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [hγH, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (γ ^ t) (S * ζ ^ i)), pow_zero,
    AlgEquiv.one_apply, map_mul, hγtS, hK]
  have := sub_one_mul_sum_eq ω p hω1 hωp
  rw [← hS] at this
  linear_combination (-(ζ ^ i)) * this

open Classical in

theorem trace_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * (if p ^ (L - m) ∣ i then ζ ^ i else 0) := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := GlobalTheory.NTr.sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · have h1 : (ζ ^ p ^ m) ^ i = 1 := by
      obtain ⟨j, hj⟩ := hd
      rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in

theorem key_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (ζ ^ i - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  rw [trace_mono p L m hm1 hm ζ hζ τ hτ i]
  split_ifs with hd
  · exact ⟨0, Subring.zero_mem _, ζ ^ i, by simp, rfl⟩
  · obtain ⟨H, hH, e⟩ := mono p hp2 L m hm1 ζ hζ γ hγ i hd
    exact ⟨H, hH, 0, by rw [sub_zero, e], rfl⟩

open Classical in

theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val)
    (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (y - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key_mono p hp2 L m hm1 hm ζ hζ γ hγ τ hτ (Multiplicative.toAdd i)
  | zero => exact ⟨0, Subring.zero_mem _, 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    obtain ⟨H2, h2, z2, e2, f2⟩ := hy
    exact ⟨H1 + H2, Subring.add_mem _ h1 h2, z1 + z2, by rw [map_add]; linear_combination e1 + e2,
      by simp only [map_add, Finset.sum_add_distrib, f1, f2]; ring⟩
  | neg x _ hx =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    exact ⟨-H1, Subring.neg_mem _ h1, -z1, by rw [map_neg]; linear_combination -e1,
      by simp only [map_neg, Finset.sum_neg_distrib, f1]; ring⟩

theorem tate_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F F' : Ω, InZl ε p L F → IsNT ε p L m F F' →
  ∀ γ : Ω ≃ₐ[ℚ] Ω, γ (zt ε p L) = zt ε p L ^ (1 + p ^ m) → ∃ H : Ω, InZl ε p L H ∧ (p : Ω) ^ c * (F - F') = γ H - H := by
  intro p hpf hp2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ ε L m hm1 hmL F F' hF hNT γ hγ
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := GlobalTheory.NTr.zt_prim ε p L hp.pos
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨τ, hτ, hT⟩ := hNT
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨H, hH, z, e1, e2⟩ := key p hp2 L m hm1 hmL (zt ε p L) hζ γ hγ τ hτ _ hDF
  have hz : z = D * F' := by
    apply mul_left_cancel₀ hpN
    rw [← e2]
    simp only [map_mul, map_natCast, ← Finset.mul_sum]
    rw [← hT]; ring
  refine ⟨H / D, ⟨D, hD, by rwa [mul_div_cancel₀ _ hD0]⟩, ?_⟩
  rw [map_div₀, map_natCast, pow_one, ← sub_div, ← e1, hz, eq_div_iff hD0]
  ring

end GlobalTheory.TateInv
