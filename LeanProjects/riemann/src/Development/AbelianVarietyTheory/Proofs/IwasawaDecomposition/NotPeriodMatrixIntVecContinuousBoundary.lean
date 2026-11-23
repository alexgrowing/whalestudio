import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodFrame

theorem combMat_mulVec_eq_sum {g r : ℕ} (l : Fin r → Fin g → ℂ) (φ : Matrix (Fin g) (Fin r) ℚ) (v : Fin g → ℂ) :
    combMat l φ *ᵥ v = ∑ m, (∑ i, (φ i m : ℂ) * v i) • l m := by
  ext k
  simp only [combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem exists_nat_mul_int {r : ℕ} (u : Fin r → ℚ) : ∃ N : ℕ, 0 < N ∧ ∀ m, ∃ k : ℤ, (N : ℚ) * u m = k := by
  refine ⟨∏ m, (u m).den, Finset.prod_pos fun m _ => (u m).den_pos, fun m => ?_⟩
  refine ⟨(∏ j ∈ Finset.univ.erase m, (u j).den : ℕ) * (u m).num, ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m)]
  push_cast
  rw [_root_.mul_assoc, _root_.mul_comm ((u m).den : ℚ), Rat.mul_den_eq_num]

end GlobalTheory.PeriodFrame

theorem GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  intro n a g r₀ r K ζ lam M c α φ rk D hK hζa hζK hζ0 hlam hζc hM hφ hrk hD hdet v hv hsupp F hF heq
  set u : Fin r → ℚ := fun m => ∑ i, φ i m * (v i : ℚ) with hu
  obtain ⟨N, hN0, hNint⟩ := GlobalTheory.PeriodFrame.exists_nat_mul_int u
  choose kk hkk using hNint
  set W : (Fin n → ℂ) → Fin g → ℂ := fun z => ((N : ℂ) / D) • (GlobalTheory.PeriodFrame.combMat (ζ z) α *ᵥ F z) with hW
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hζc0 : ContinuousAt ζ 0 := (hζa 0 h0).continuousAt
  have hFc0 : ContinuousAt F 0 := hF.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hWc : ContinuousAt W 0 := by
    have h1 : ∀ m k, ContinuousAt (fun z => ζ z m k) 0 := fun m k =>
      (continuous_apply k).continuousAt.comp ((continuous_apply m).continuousAt.comp hζc0)
    have h2 : ∀ i, ContinuousAt (fun z => F z i) 0 := fun i => (continuous_apply i).continuousAt.comp hFc0
    refine continuousAt_pi.2 fun k => ?_
    simp only [hW, GlobalTheory.PeriodFrame.combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hlK : ∀ᶠ b in 𝓝 (0 : Fin n → ℂ), ∀ j, ζ b j ∈ K b := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with b hb using hζK b hb
  have hev := IsLatFam.eventually_intComb hK h0 hζc0 hlK hζ0 (W 0)
  have ht : Filter.Tendsto (fun z => (z, W z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 ((0 : Fin n → ℂ), W 0)) :=
    (continuousAt_id.prodMk hWc).tendsto
  have hev2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
      (W z ∈ K z → ∃ m : Fin r₀ → ℤ, W z = ∑ j, m j • ζ z j) :=
    Filter.Eventually.and (Metric.isOpen_ball.mem_nhds h0 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1)
      (ht.eventually hev)
  set s : ℝ → Fin n → ℂ := fun R k => if (k : ℕ) < a then -(R : ℂ) else 0 with hs
  have hsdom : ∀ R : ℝ, 0 < R → s R ∈ logDom n a := by
    intro R hR k
    by_cases hk : (k : ℕ) < a
    · simp [hs, hk, hR]
    · simp [hs, hk]
  have hslim : Filter.Tendsto (fun R => logExp a (s R)) Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hs, hk, if_true, Pi.zero_apply]
      have h3 : Filter.Tendsto (fun R : ℝ => ((Real.exp (-R) : ℝ) : ℂ)) Filter.atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      simpa [Complex.ofReal_exp] using h3
    · simp [logExp, hs, hk]
  obtain ⟨R, ⟨hzb, hzK⟩, hR0⟩ := ((hslim.eventually hev2).and (Filter.eventually_gt_atTop 0)).exists
  have hs0 := hsdom R hR0
  have he := heq (s R) hs0 hzb
  have hWz : W (logExp a (s R)) = ∑ m, ((kk m : ℤ) : ℂ) • lam (s R) m := by
    have hP := hdet (s R) hs0
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsm : ∀ (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
      intro c A x; ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
    simp only [hW]
    rw [← he, GlobalTheory.PeriodFrame.perTau, Matrix.mulVec_mulVec, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, hsm, smul_smul,
      GlobalTheory.PeriodFrame.combMat_mulVec_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    have h4 := congrArg (Rat.cast : ℚ → ℂ) (hkk m)
    push_cast [hu] at h4
    rw [← h4]
    field_simp

  have hWK : W (logExp a (s R)) ∈ K (logExp a (s R)) :=
    ((hlam (s R) hs0).2 _).2 ⟨kk, by rw [hWz]; exact Finset.sum_congr rfl fun m _ => Int.cast_smul_eq_zsmul ℂ _ _⟩
  obtain ⟨mm, hmm⟩ := hzK hWK
  have hcomb : ∑ j, kk j • lam (s R) j = ∑ j, (∑ i, mm i * c i j) • lam (s R) j := by
    have e1 : ∑ j, kk j • lam (s R) j = W (logExp a (s R)) := by
      rw [hWz]; exact Finset.sum_congr rfl fun m _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [e1, hmm]
    simp only [hζc (s R) hs0, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hkc : ∀ j, kk j = ∑ i, mm i * c i j := by
    have hli := (hlam (s R) hs0).1
    have h5 := Fintype.linearIndependent_iff.1 hli (fun j => ((kk j - ∑ i, mm i * c i j : ℤ) : ℝ)) (by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, hcomb, sub_self])
    intro j
    have h6 := h5 j
    have h7 : kk j - ∑ i, mm i * c i j = 0 := by exact_mod_cast h6
    exact sub_eq_zero.1 h7
  set cq := c.map (Int.cast : ℤ → ℚ) with hcq
  set Mq := M.map (Int.cast : ℤ → ℚ) with hMq
  set vq : Fin g → ℚ := fun i => (v i : ℚ) with hvq
  set mq : Fin r₀ → ℚ := fun i => (mm i : ℚ) with hmq
  have hvec : Matrix.vecMul ((N : ℚ) • vq) φ = Matrix.vecMul mq cq := by
    ext j
    have h6 := hkk j
    rw [hkc j] at h6
    push_cast at h6
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hcq, hvq, hmq, Matrix.map_apply]
    rw [← h6, hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hskew : cq * (Mq * (α * cq)ᵀ) = -((α * cq) * Mq * cqᵀ)ᵀ := by
    have hMt : Mqᵀ = -Mq := by
      ext i j
      have h := congrFun (congrFun hM i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
      simp [hMq, Matrix.transpose_apply, h]
    rw [Matrix.transpose_mul (α * cq * Mq), Matrix.transpose_transpose, Matrix.transpose_mul (α * cq) Mq, hMt]
    simp [Matrix.neg_mul, Matrix.mul_neg]
  have hfin := congrArg (fun x => Matrix.vecMul x (Mq * (α * cq)ᵀ)) hvec
  simp only [Matrix.vecMul_vecMul] at hfin
  rw [show φ * (Mq * (α * cq)ᵀ) = 1 by rw [← Matrix.mul_assoc, hφ], Matrix.vecMul_one, hskew] at hfin
  apply hv
  funext i
  by_cases hi : i.val < rk
  · have h7 := congrFun hfin i
    have h8 : Matrix.vecMul mq (-((α * cq) * Mq * cqᵀ)ᵀ) i = 0 := by
      simp only [Matrix.vecMul, dotProduct, Matrix.neg_apply, Matrix.transpose_apply, hrk i hi, neg_zero, mul_zero,
        Finset.sum_const_zero]
    rw [h8] at h7
    simp only [Pi.smul_apply, smul_eq_mul, hvq] at h7
    have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have h9 := (mul_eq_zero.1 h7).resolve_left hN
    simpa using h9
  · exact hsupp i (not_lt.1 hi)
