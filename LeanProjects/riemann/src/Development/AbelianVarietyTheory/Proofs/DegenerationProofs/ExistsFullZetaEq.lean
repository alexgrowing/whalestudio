import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ReZeta

theorem exists_exponent {K : Type} [Field K] (ξ ζ : ℕ → Kˣ) (hξ : ∀ n, 0 < n → IsPrimitiveRoot (ξ n) n)
    (hξ' : ∀ n m, 0 < n → 0 < m → ξ (n * m) ^ m = ξ n) (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) :
    ∃ ν : ℕ → ℤ, (∀ n, 0 < n → ξ n ^ ν n = ζ n) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
  have h : ∀ n : ℕ, ∃ i : ℕ, 0 < n → ξ n ^ i = ζ n := fun n => by
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (hξ n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity n (ζ n)).2 (hζ n hn).pow_eq_one)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose i hi using h
  refine ⟨fun n => i n, fun n hn => by rw [zpow_natCast, hi n hn], fun n hn => ?_, fun n m hn hm => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (((hξ n hn).pow_iff_coprime hn _).1 (hi n hn ▸ hζ n hn))
  · rw [← (hξ n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, hi n hn, mul_inv_eq_one,
      ← hξ' n m hn hm, ← pow_mul, mul_comm m, pow_mul, hi _ (Nat.mul_pos hn hm), hζ' n m hn hm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem modN_smul (D : Datum H) {n : ℕ} {c : 𝓞 E} (h : (n : 𝓞 E) ∣ c) (a : D.La) : D.ModN n (c • a) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b • a, by rw [mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem exists_sim (D : Datum H) (ν : ℕ → ℤ) (h₁ : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h₂ : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) : ∃ g : Sim D, g.ν = ν := by
  obtain ⟨t, ht₁, ht₂, -⟩ := GlobalTheory.NormTower.exists_norm_tower E H (GlobalTheory.HostModel.level H 1 one_pos) ν h₁ h₂
  refine ⟨⟨fun n => t n • LinearMap.id, ν, fun n m hn hm a => ?_, fun n hn => ?_, fun n hn a b => ?_⟩, rfl⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_smul]
    exact modN_smul D (ht₂ n m hn hm) a
  · obtain ⟨u, v, huv⟩ := h₁ n hn
    obtain ⟨c, hc⟩ := ht₁ n hn
    have huv' : (u : 𝓞 E) * (ν n : 𝓞 E) + (v : 𝓞 E) * (n : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
    have hd : (n : 𝓞 E) ∣ (u : 𝓞 E) * H.bar (t n) * t n - 1 :=
      ⟨u * c - v, by linear_combination (u : 𝓞 E) * hc + huv'⟩
    refine ⟨((u : 𝓞 E) * H.bar (t n)) • LinearMap.id, fun a => ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have := modN_smul D hd a
    rw [sub_smul, one_smul] at this
    exact ⟨by rwa [← mul_smul], by rwa [← mul_smul, mul_comm]⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨c, hc⟩ := ht₁ n hn
    have e : H.bar (t n) * t n = (ν n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    refine ⟨D.EF a (c • b), ?_⟩
    rw [D.adj, ← mul_smul, e, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_add,
      map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul, add_sub_cancel_left]

end GlobalTheory.ReZeta
