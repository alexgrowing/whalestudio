import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
