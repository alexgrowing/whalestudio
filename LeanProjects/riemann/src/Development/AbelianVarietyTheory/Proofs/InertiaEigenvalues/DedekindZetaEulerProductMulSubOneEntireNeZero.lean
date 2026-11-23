import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
private lemma dedekindZeta_eq_exp_tsum_neg_log (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h] at hs
    norm_num at hs
  have key := _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs
  rw [_root_.GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs]
  convert key using 1
  · refine tsum_congr fun I => ?_
    by_cases hI : I = ⊥
    · simp [hI, Complex.zero_cpow hs0]
    · simp [hI]
  · congr 1
    refine tsum_congr fun P => ?_
    simp [P.ne_bot]

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero :
    ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _
  obtain ⟨Z, hZd, hZ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  refine ⟨Z, hZd, ?_, hZ⟩
  have h1 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := hZd.continuous.comp Complex.continuous_ofReal
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    rw [hZ s hs', dedekindZeta_eq_exp_tsum_neg_log K s hs']
  rw [tendsto_nhds_unique h1 h2]
  exact_mod_cast dedekindZeta_residue_ne_zero K

end GlobalTheory
