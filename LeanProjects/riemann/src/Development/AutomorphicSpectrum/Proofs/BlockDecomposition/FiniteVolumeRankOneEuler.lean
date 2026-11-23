import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandardStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero

open GlobalTheory.CompanionTheory.SW.Growth

section Abstract
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M : ℕ}

theorem growth_of_scale (b : Module.Basis (Fin d) F E)
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hscale : ∀ (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e →
      ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) →
      μ v (dilSet b v a) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * μ v (latV b v))
    (hfin : ∀ v, μ v (latV b v) < ⊤)
    (hsum : Summable fun v => |(μ v (latV b v)).toReal - 1|)
    (hne : ∀ v, μ v ≠ 0) :
    (∀ a : ℕ, 0 < a → ∀ v, μ v (dilSet b v a) < ⊤) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧
        κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (μ v (dilSet b v a)).toReal := by
  have hdil : ∀ (a : ℕ), 0 < a → ∀ v, μ v (dilSet b v a) < ⊤ := by
    intro a ha v
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) a ha
    rw [hscale v a (e v) ha (he v).1 (he v).2]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin v)
  have hpos : ∀ v, 0 < (μ v (latV b v)).toReal := by
    intro v
    obtain ⟨n, hn, hnz⟩ := exists_pos_mass b v (μ v) (hne v)
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) n hn
    have hz : μ v (latV b v) ≠ 0 := by
      intro h0
      rw [hscale v n (e v) hn (he v).1 (he v).2, h0, mul_zero] at hnz
      exact hnz rfl
    exact ENNReal.toReal_pos hz (hfin v).ne
  obtain ⟨hmulL, -, hprodpos, -⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ (fun v => (μ v (latV b v)).toReal) hsum
  refine ⟨hdil, ∏' v, (μ v (latV b v)).toReal, hprodpos hpos, fun k => ⟨k + 1, Nat.lt_succ_self k, ?_⟩⟩
  set a := k + 1 with hadef
  have ha : 0 < a := Nat.succ_pos k
  obtain ⟨e, he, hfs, hprod⟩ := exists_exponents (F := F) a ha
  have hid : ∀ v, (μ v (dilSet b v a)).toReal =
      (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2) * (μ v (latV b v)).toReal := by
    intro v
    rw [hscale v a (e v) ha (he v).1 (he v).2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), pow_mul]
  have hf2 : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    hfs.fun_comp (g := fun y : ℝ => y ^ (2 * M - 2)) (one_pow _)
  have hmul : Multipliable
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    (hasProd_prod_of_ne_finset_one (s := Set.Finite.toFinset hf2) (fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset hf2).2 h))).multipliable
  rw [tprod_congr hid, hmul.tprod_mul hmulL, tprod_eq_finprod hf2, ← finprod_pow hfs, hprod, ← pow_mul,
    mul_comm]

end Abstract

theorem growth_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) → (∀ a : ℕ, 0 < a → ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm hne
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_volume_rank_one_product F E σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hscale := fun (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ) (ha : 0 < a) h1 h2 =>
    GlobalTheory.T.local_volume_rank_one_standard F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v) a e ha h1 h2
  exact growth_of_scale b (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))
    hscale hfin hsum hne

end GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero
