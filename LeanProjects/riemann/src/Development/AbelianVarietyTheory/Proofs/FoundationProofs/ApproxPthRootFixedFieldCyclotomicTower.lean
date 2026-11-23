import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TopRoots

theorem approxRoot_fix_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) →
    0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  intro p _ Ω _ _ hp2 hclo T v hv _ hp1
  classical
  have hpp : p.Prime := Fact.out
  let S : Set Ω := Set.range T.ζ ∪ Set.range T.qq
  let B := Algebra.adjoin (O0 p) S
  let F := Fix Ω (⨅ n, Gn T n)

  have hBle : B ≤ integralClosure (O0 p) Ω := by
    rw [Algebra.adjoin_le_iff]
    rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [(T.prim n).pow_eq_one]; exact isIntegral_one
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [Basic.qq_pow]; exact isIntegral_algebraMap
  have hBint : ∀ x ∈ B, v x ≤ 1 := fun x hx => (hv x).2 (hBle hx)

  have hBF : ∀ x ∈ B, x ∈ F := by
    intro x hx g
    have hg : (g : Gal p Ω) ∈ ⨅ n, Gn T n := g.2
    rw [Subgroup.mem_iInf] at hg
    have hle : B ≤ AlgHom.equalizer (g : Gal p Ω).toAlgHom (AlgHom.id (O0 p) Ω) := by
      rw [Algebra.adjoin_le_iff]
      rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · exact ((Basic.mem_gn T n _).1 (hg n)).1
      · exact ((Basic.mem_gn T n _).1 (hg n)).2
    have := hle hx
    rw [AlgHom.mem_equalizer] at this
    exact this

  set θ := v (T.ζ 1 - 1) with hθ
  have hz1 := GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 1 le_rfl
  have hθ1 : θ < 1 := hz1.1
  let good : Ω → Prop := fun x => ∃ w ∈ F, v (x - w ^ p) ≤ θ * v x

  have hgoodB : ∀ x ∈ B, v (p : Ω) ≤ θ * v x → good x := by
    intro x hx hvx
    obtain ⟨y, hy, z, hz, e⟩ := GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower p Ω T x hx
    refine ⟨y, hBF y hy, ?_⟩
    have : x - y ^ p = (p : Ω) * z := by rw [e]; ring
    rw [this, map_mul]
    calc v (p : Ω) * v z ≤ v (p : Ω) * 1 := mul_le_mul_of_nonneg_left (hBint z hz) zero_le
      _ = v (p : Ω) := mul_one _
      _ ≤ θ * v x := hvx

  have hunit : ∀ u ∈ B, ∀ u' ∈ B, u * u' = 1 → good u := by
    intro u hu u' hu' e
    have hvu : v u = 1 := by
      have h1 := hBint u hu
      have h2 := hBint u' hu'
      have h3 : v u * v u' = 1 := by rw [← map_mul, e, map_one]
      by_contra hne
      have hlt : v u < 1 := lt_of_le_of_ne h1 hne
      have : v u * v u' < 1 := by
        calc v u * v u' ≤ v u * 1 := mul_le_mul_of_nonneg_left h2 zero_le
          _ = v u := mul_one _
          _ < 1 := hlt
      exact absurd h3 (ne_of_lt this)
    refine hgoodB u hu ?_
    rw [hvu, mul_one]
    calc v (p : Ω) ≤ θ * v (T.ζ 1 - 1) := hz1.2
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hθ1.le zero_le
      _ = θ := mul_one _

  have hzeta : ∀ n, 1 ≤ n → good (T.ζ n - 1) := by
    intro n hn
    have hmem : T.ζ n - 1 ∈ B :=
      Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)) (Subalgebra.one_mem _)
    exact hgoodB _ hmem (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 n hn).2

  have hB : ∀ b ∈ B, good b := by
    intro b hb
    by_cases hb0 : b = 0
    · refine ⟨0, F.zero_mem, ?_⟩
      rw [hb0, zero_pow hpp.ne_zero, sub_zero, map_zero]; exact zero_le
    obtain ⟨n, k, hn, u, hu, u', hu', e, rfl⟩ := GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer p Ω hclo T b hb hb0
    have h1 := hunit u hu u' hu' e
    have h2 := (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hzeta n hn) (hzeta n hn)).2.2 k
    exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ h1 h2).1

  refine ⟨θ, hθ1, fun x hx => ?_⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hclo
  haveI : IsAlgClosed Ω := hclo.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hclo.alg
  have hfix : ∀ g : Ω ≃ₐ[O0 p] Ω, (∀ s ∈ S, g s = s) → g x = x := by
    intro g hg
    have hgm : g ∈ ⨅ n, Gn T n := by
      rw [Subgroup.mem_iInf]
      intro n
      exact (Basic.mem_gn T n g).2
        ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩
    exact hx ⟨g, hgm⟩
  obtain ⟨b, hb, c, hc, hc0, rfl⟩ := GlobalTheory.T.exists_div_mem_adjoin_of_fixed (O0 p) Ω hclo.inj S x hfix
  exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hB b hb) (hB c hc)).2.1 hc0

end GlobalTheory.K5.TopRoots
