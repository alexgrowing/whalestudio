import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem bigSizes_of (g N r : ℕ) (hN : 1 + 2 * g * 2 ^ g < N)
    (hr : 6 * (N ^ g * g.factorial) + 2 * (N ^ g * g.factorial) * (g * 4 ^ g) < r) :
    1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N ∧
    2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N
      < (r * N : ℕ) ∧
    6 * (N ^ g * g.factorial) < r * N := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have e1 : (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e2 : (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ 2 ^ g := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e3 : (3 / 2 : ℝ) ^ g ≤ 2 ^ g := pow_le_pow_left₀ (by norm_num) (by norm_num) g
  have hNpos : 0 < N := by omega
  refine ⟨?_, ?_, ?_⟩
  · have hN' : ((1 + 2 * g * 2 ^ g : ℕ) : ℝ) < N := by exact_mod_cast hN
    push_cast at hN'
    have : 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) ≤ 2 * g * 2 ^ g := by gcongr
    linarith
  · set X : ℕ := N ^ g * g.factorial
    have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
    have hr' : ((6 * X + 2 * X * (g * 4 ^ g) : ℕ) : ℝ) < r := by exact_mod_cast hr
    push_cast at hr'
    have hC : (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) ≤ g * 4 ^ g := by
      have h4 : (4 : ℝ) ^ g = 2 ^ g * 2 ^ g := by rw [← mul_pow]; norm_num
      rw [h4, ← _root_.mul_assoc]
      have hp1 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ g := by positivity
      have hp2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by positivity
      gcongr
    have h1 : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) < r := by
      have : 2 * (X : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1))
          ≤ 2 * X * (g * 4 ^ g) := by gcongr
      have h6 : (0 : ℝ) ≤ 6 * X := by positivity
      linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    push_cast
    exact mul_lt_mul_of_pos_right h1 hNr
  · have h1 : 6 * (N ^ g * g.factorial) < r := by omega
    calc 6 * (N ^ g * g.factorial) < r := h1
      _ ≤ r * N := Nat.le_mul_of_pos_right r hNpos

theorem bigSizes : ∀ (g n : ℕ), n.Prime → Odd n → ∃ k j : ℕ, 2 ≤ k ∧ 1 ≤ j ∧ ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  intro g n hp _
  have hn : 1 < n := hp.one_lt
  set k := (1 + 2 * g * 2 ^ g) + 2 with hk
  set N₀ := (n ^ k) ^ 2 with hN₀
  set M := 6 * (N₀ ^ g * g.factorial) + 2 * (N₀ ^ g * g.factorial) * (g * 4 ^ g) with hM
  refine ⟨k, M + 1, by omega, by omega, ?_⟩
  intro o Ω _ _ _ S hg hN hr
  have hkN : 1 + 2 * g * 2 ^ g < N₀ := by
    have h1 : k < n ^ k := Nat.lt_pow_self hn
    have h2 : n ^ k ≤ (n ^ k) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hjr : M < n ^ (M + 1) := by
    have := Nat.lt_pow_self (n := M + 1) hn
    omega
  unfold GlobalTheory.ZH.ThetaSys.Big
  rw [hg, hN, hr]
  exact bigSizes_of g N₀ (n ^ (M + 1)) hkN hjr

end GlobalTheory.Mum
