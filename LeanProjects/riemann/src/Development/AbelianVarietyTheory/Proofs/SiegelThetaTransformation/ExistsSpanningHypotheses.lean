import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SpanInhab

theorem exists_imag_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

theorem exists_prime_jacobi_neg {d : ℕ} (hd : Odd d) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = 1 := by
  obtain ⟨p, hp, hN, hm⟩ := Nat.exists_prime_gt_modEq_one (k := 4 * d) N (by have := hd.pos; omega)
  have h4 : p % 4 = 1 := hm.of_mul_right d
  have hpd : p ≡ 1 [MOD d] := hm.of_mul_left 4
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  refine ⟨p, hN, hp, ?_⟩
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_one_mod_four h4, _root_.one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four h4 hd,
    jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast hpd), jacobiSym.one_left]

theorem exists_split_cover {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) :
    ∃ (pd : ℕ) (J : Ideal (𝓞 E)) (l₂ : Geo.Tor.Level H) (c : Coeff l) (c₂ : Coeff l₂), pd.Prime ∧ 3 < pd ∧
      c₂.F = c.F ∧ l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ pd.Coprime l.M ∧ l₂.Mb = l.Mb * J ∧
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ l₂.A = l.A := by
  have hM := l.three_le
  obtain ⟨p, hN, hp, hj⟩ := exists_prime_jacobi_neg (d := H.d) (Nat.odd_iff.2 (by have := H.d_mod; omega)) l.M
  have hco : p.Coprime l.M := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  obtain ⟨J, h1, h2, h3⟩ := (GlobalTheory.exists_level_mul_split E H l).2 p hp (by omega) hj
  obtain ⟨l₂, hd, hM₂, hMb, hA⟩ := (GlobalTheory.exists_level_mul_split E H l).1 p J (hp.odd_of_ne_two (by omega)) hco h1 h2 h3
  let c₂ : Coeff l₂ := LevelExist.minCoeff l₂
  have hz : zeta l.M' ∈ c₂.F := by
    obtain ⟨k, hk⟩ := LevelExist.zeta_eq_pow_of_dvd (LevelExist.M'_pos l₂)
      (show l.M' ∣ l₂.M' from Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)))
    rw [hk]
    exact pow_mem c₂.zeta_mem k
  have hle : KA l ≤ c₂.F := by
    have := c₂.le
    unfold KA at this ⊢
    rwa [hA] at this
  exact ⟨p, J, l₂, ⟨c₂.F, c₂.fin, c₂.conj, hz, hle⟩, c₂, hp, by omega, rfl, hd, hM₂, hco, hMb, h3, hA⟩

end GlobalTheory.SpanInhab
