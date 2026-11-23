import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace StokesLimitEps

open Matrix

theorem coeff_tendsto {N : ℕ} (c : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), f q t = ∑ i ∈ Finset.range N, c i t * (1 / (q : ℝ)) ^ i)
    (hg : ∀ q : ℕ, 1 ≤ q → Tendsto (f q) (𝓝[>] 0) (𝓝 (g q))) :
    ∃ ℓ : ℕ → ℝ, (∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i))) ∧
      ∀ q : ℕ, 1 ≤ q → g q = ∑ i ∈ Finset.range N, ℓ i * (1 / (q : ℝ)) ^ i := by

  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k h
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at h
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : ℝ → Fin N → ℝ := fun t j => f ((j : ℕ) + 1) t

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun i : Fin N => c i t) = (Matrix.vandermonde x)⁻¹ *ᵥ F t := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N => hf ((j : ℕ) + 1) (by omega)] with t ht
    have hval : F t = Matrix.vandermonde x *ᵥ fun i : Fin N => c i t := by
      funext j
      simp only [F, ht j, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, x]
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i t * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hF : Tendsto F (𝓝[>] 0) (𝓝 fun j : Fin N => g ((j : ℕ) + 1)) :=
    tendsto_pi_nhds.2 fun j => hg _ (by omega)
  have hC : Tendsto (fun t => fun i : Fin N => c i t) (𝓝[>] 0)
      (𝓝 ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1))) :=
    (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp hF).congr' (hev.mono fun t ht => ht.symm)
  let ℓ : ℕ → ℝ := fun i => if h : i < N then
    ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1)) ⟨i, h⟩ else 0
  have hℓ : ∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i)) := by
    intro i hi
    simpa only [ℓ, dif_pos hi] using tendsto_pi_nhds.1 hC ⟨i, hi⟩
  refine ⟨ℓ, hℓ, fun q hq => tendsto_nhds_unique (hg q hq) ?_⟩
  refine Tendsto.congr' ((hf q hq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun i hi => (hℓ i (Finset.mem_range.1 hi)).mul_const _

theorem tendsto_const_coeff {N : ℕ} (ℓ : ℕ → ℝ) (hN : 1 ≤ N) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range N, ℓ i * (1 / ((m + 1 : ℕ) : ℝ)) ^ i) atTop (𝓝 (ℓ 0)) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs := tendsto_finsetSum (Finset.range N) fun i _ => (h0.pow i).const_mul (ℓ i)
  have e : ∑ i ∈ Finset.range N, ℓ i * (0 : ℝ) ^ i = ℓ 0 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
      (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  rwa [e] at hs

end StokesLimitEps

theorem StokesLimitEps.proof (hT : StokesLimitT.Statement) (hTop : TopNPoly.Statement)
    (hOm : OmNPoly.Statement) (hMu : MuMeasureLimit.Statement) : StokesLimitEps.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII hAr
  have hTq := fun q (hq : 1 ≤ q) => hT II Ψ K ι Ω E D O Lt X B 1 q hII hAr le_rfl hq
  obtain ⟨c, hc0, hc⟩ := hTop II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨v, d, hv0, hd0, hvd⟩ := hOm II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨hmuV, hmuD⟩ := hMu II Ψ K ι Ω E D O Lt X B hII hAr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto c (fun q => X.topN B 1 q) (X.topNLim B 1) hc
      fun q hq => (hTq q hq).1
    have h0 : ℓ 0 = arLim X.H X.S B := by
      obtain ⟨L, hL⟩ := hAr
      have e1 : arLim X.H X.S B = L := by unfold arLim; exact hL.limUnder_eq
      have h := hℓ 0 (by omega)
      rw [hc0] at h
      rw [e1]; exact tendsto_nhds_unique h hL
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 2) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto v (fun q => X.Vb B 1 q) (X.VbLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.1) fun q hq => (hTq q hq).2.1
    have h0 : ℓ 0 = meanU X.H X.Cd * degMu X.H / 2 := by
      have h := hℓ 0 (by omega)
      rw [hv0] at h
      exact tendsto_nhds_unique h hmuV
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto d (fun q => X.degN B 1 q) (X.degNLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.2) fun q hq => (hTq q hq).2.2
    have h0 : ℓ 0 = degMu X.H := by
      have h := hℓ 0 (by omega)
      rw [hd0] at h
      exact tendsto_nhds_unique h hmuD
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
