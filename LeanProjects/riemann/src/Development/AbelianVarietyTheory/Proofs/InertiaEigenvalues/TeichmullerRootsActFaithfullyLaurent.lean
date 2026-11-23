import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem

noncomputable section
namespace GlobalTheory.DeltaInv
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PsiShiftProof GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters

theorem root_eq {l : ℕ} [hl : Fact l.Prime] {z w : ℤ_[l]} (hz : z ^ (l - 1) = 1) (hw : w ^ (l - 1) = 1)
    (h : PadicInt.toZMod z = PadicInt.toZMod w) : z = w :=
  by
  have hn : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  have key : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) * (z - w) = 0 := by
    rw [geom_sum₂_mul, hz, hw, sub_self]
  have hres : PadicInt.toZMod (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) =
      ((l - 1 : ℕ) : ZMod l) * PadicInt.toZMod z ^ (l - 1 - 1) := by
    rw [map_sum, Finset.sum_congr rfl (g := fun _ => PadicInt.toZMod z ^ (l - 1 - 1))]
    · simp
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega
  have hz0 : PadicInt.toZMod z ≠ 0 := by
    intro h0
    have h1 := congrArg PadicInt.toZMod hz
    rw [map_pow, h0, zero_pow hn.ne', map_one] at h1
    exact zero_ne_one h1
  have hl0 : ((l - 1 : ℕ) : ZMod l) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff (ZMod l) l _).mp h0)
    omega
  have hs : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) ≠ 0 := by
    intro h0
    apply mul_ne_zero hl0 (pow_ne_zero _ hz0)
    rw [← hres, h0, map_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs)

theorem exists_mul_pow {k : Type} [Field k] (c : k⸨X⸩) (t : k⟦X⟧) :
    ∃ (N : ℕ) (b : k⟦X⟧), (vv k * (t : k⸨X⸩)) ^ N * c = (b : k⸨X⸩) :=
  by
  refine ⟨(-c.order).toNat, PowerSeries.X ^ c.order.toNat * t ^ (-c.order).toNat * c.powerSeriesPart, ?_⟩
  have hc := LaurentSeries.single_order_mul_powerSeriesPart c
  have hN : ((-c.order).toNat : ℤ) + c.order = (c.order.toNat : ℤ) := by omega
  have hs : ∀ n : ℕ, (HahnSeries.single (1 : ℤ) (1 : k)) ^ n = HahnSeries.single (n : ℤ) 1 := by
    intro n
    rw [HahnSeries.single_pow]
    simp
  conv_lhs => arg 2; rw [← hc]
  rw [vv_eq_coe_X, map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_X, mul_pow, hs, hs]
  calc (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * (t : k⸨X⸩) ^ (-c.order).toNat) *
        (HahnSeries.single c.order 1 * (c.powerSeriesPart : k⸨X⸩))
      = (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * HahnSeries.single c.order 1) *
          (t : k⸨X⸩) ^ (-c.order).toNat * (c.powerSeriesPart : k⸨X⸩) := by ring
    _ = _ := by rw [HahnSeries.single_mul_single, hN, one_mul]

theorem coeff_one_opp (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (z : ℤ_[l]) :
    PowerSeries.coeff 1 (onePlusPow k l z) = ZMod.castHom (dvd_refl l) k (PadicInt.toZMod z) :=
  by
  unfold onePlusPow
  rw [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, smul_eq_mul, mul_one]
  rfl

theorem main (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l)
    (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) :
    ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩),
      (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧
      Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c :=
  by
  have hne : l - 1 ≠ 0 := (Nat.sub_pos_of_lt hl.out.one_lt).ne'
  set σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩) :=
    fun z => GlobalTheory.PsiShiftProof.delPi k (Units.ofPowEqOne z.1 (l - 1) z.2 hne) with hσ
  have hσc : ∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩) := by
    intro z b
    rw [hσ, GlobalTheory.PsiShiftProof.delPi_coe]
    rfl
  have hinj : Function.Injective (fun b : k⟦X⟧ => (b : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective
  have hfix : ∀ z (a : k⟦X⟧), σ z (ι (a : k⸨X⸩)) = ι (a : k⸨X⸩) := by
    intro z a
    obtain ⟨b, hb⟩ := H.2.1 a
    rw [hb, hσc, (H.2.2.1 b).2 ⟨a, hb⟩ z.1 z.2]
  have hιv : ∀ z, σ z (ι (vv k)) = ι (vv k) := by
    intro z
    rw [vv_eq_coe_X, hfix]
  have hv0 : ι (vv k) ≠ 0 := by
    exact (map_ne_zero ι).mpr (vv_ne_zero k)
  refine ⟨σ, hσc, ?_, ?_⟩
  · intro z w hzw
    have h1 := congrArg (fun f : k⸨X⸩ →+* k⸨X⸩ => f (1 + vv k)) hzw
    simp only [hσ, GlobalTheory.PsiShiftProof.del_one_add] at h1
    have h2 := congrArg (PowerSeries.coeff 1) (hinj h1)
    simp only [Units.val_ofPowEqOne, coeff_one_opp] at h2
    exact Subtype.ext (root_eq z.2 w.2 ((ZMod.castHom (dvd_refl l) k).injective h2))
  · intro c
    constructor
    · intro hc
      obtain ⟨u, hu⟩ := H.1
      obtain ⟨N, b, hb⟩ := exists_mul_pow c ((u : k⟦X⟧) * PowerSeries.X ^ (l - 2))
      have hv : vv k * (((u : k⟦X⟧) * PowerSeries.X ^ (l - 2) : k⟦X⟧) : k⸨X⸩) = ι (vv k) := by
        rw [hu, map_mul, map_pow, ← vv_eq_coe_X]
        have : l - 1 = (l - 2) + 1 := by have := hl.out.two_le; omega
        rw [this, pow_succ]
        ring
      rw [hv] at hb
      have hbinv : ∀ z : ℤ_[l], z ^ (l - 1) = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b = b := by
        intro z hz
        apply hinj
        show ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b : k⟦X⟧) : k⸨X⸩) = (b : k⸨X⸩)
        have e := hσc ⟨z, hz⟩ b
        dsimp only at e
        rw [← e, ← hb, map_mul, map_pow, hc, hιv]
      obtain ⟨a, ha⟩ := (H.2.2.1 b).1 hbinv
      refine ⟨(a : k⸨X⸩) * (vv k ^ N)⁻¹, ?_⟩
      rw [map_mul, map_inv₀, map_pow, ha, ← hb]
      field_simp
    · rintro ⟨c₀, rfl⟩ z
      obtain ⟨N, b, hb⟩ := exists_mul_pow c₀ 1
      rw [map_one, mul_one] at hb
      have h1 := congrArg ι hb
      rw [map_mul, map_pow] at h1
      have h2 := congrArg (σ z) h1
      rw [map_mul, map_pow, hfix, ← h1, show σ z (ι (vv k)) = ι (vv k) from hιv z] at h2
      exact mul_left_cancel₀ (pow_ne_zero N hv0) h2

end GlobalTheory.DeltaInv
