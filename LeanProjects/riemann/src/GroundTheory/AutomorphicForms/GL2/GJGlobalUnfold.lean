import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfoldSetup

open MeasureTheory Set Function NumberField Filter Topology
open scoped ENNReal NNReal NumberField.AdeleRing

namespace GroundTheory.Automorphic.GJGlobal

noncomputable section

namespace UnfoldGL

open Reduction AutomorphicForm RightCosetSpace RankDecomp CuspidalSpectrum

theorem measurable_tsum_of_summable {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℂ} (hf : ∀ i, Measurable (f i)) (hs : ∀ x, Summable fun i => f i x) :
    Measurable fun x => ∑' i, f i x := by
  have hlim : Tendsto (fun s : Finset ι => fun x => ∑ i ∈ s, f i x) atTop
      (𝓝 fun x => ∑' i, f i x) :=
    tendsto_pi_nhds.2 fun x => (hs x).hasSum
  exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun i _ => hf i) hlim

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def ratEquiv : GL (Fin n) K ≃ rationalGLOne K n :=
  Equiv.ofBijective (fun γ => ⟨ratOne K n γ, mem_rationalGLOne_iff.2 ⟨γ, rfl⟩⟩)
    ⟨fun _ _ h => ratOne_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨γ, hγ⟩ := mem_rationalGLOne_iff.1 x.2
      exact ⟨γ, Subtype.ext hγ⟩⟩

instance countable_matrix : Countable (Matrix (Fin n) (Fin n) K) := by
  have := GroundTheory.Global.countable_numberField K
  exact inferInstanceAs (Countable (Fin n → Fin n → K))

instance countable_R (k : ℕ) : Countable (R (K := K) (n := n) k) := Subtype.countable

@[simp] theorem coe_ratEquiv (γ : GL (Fin n) K) : ((ratEquiv γ : rationalGLOne K n) : normOneGL K n) = ratOne K n γ :=
  rfl

def thetaR (k : ℕ) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (y : AdelicGLn.AdelicGL K n)
    (h : normOneGL K n) : ℂ :=
  ∑' Z : R (K := K) (n := n) k, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
    ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))

def reps (k : ℕ) (g : normOneGL K n) : Set (GL (Fin n) K) :=
  {γ | ratOne K n γ * g ∈ fundamentalDomain (parabolicOne K n k)}

theorem existsUnique_reps (k : ℕ) (g : normOneGL K n) (γ₀ : GL (Fin n) K) :
    ∃! p : parabolic (K := K) (n := n) k, (p : GL (Fin n) K) * γ₀ ∈ reps k g := by
  obtain ⟨q, hq, hqu⟩ := existsUnique_smul_mem_fundamentalDomain (parabolicOne K n k) (ratOne K n γ₀ * g)
  obtain ⟨p, hp, hpq⟩ := mem_parabolicOne_iff.1 q.2
  refine ⟨⟨p, hp⟩, ?_, ?_⟩
  · show ratOne K n (p * γ₀) * g ∈ fundamentalDomain (parabolicOne K n k)
    rw [map_mul, mul_assoc, hpq]
    exact hq
  · rintro ⟨p', hp'⟩ h
    have h' : (⟨ratOne K n p', ⟨p', hp', rfl⟩⟩ : parabolicOne K n k) • (ratOne K n γ₀ * g) ∈
        fundamentalDomain (parabolicOne K n k) := by
      show ratOne K n p' * (ratOne K n γ₀ * g) ∈ fundamentalDomain (parabolicOne K n k)
      rw [← mul_assoc, ← map_mul]
      exact h
    have := hqu _ h'
    refine Subtype.ext (ratOne_injective ?_)
    rw [hpq]
    exact congrArg Subtype.val this

def rankEquiv {k : ℕ} (hk : k ≤ n) (g : normOneGL K n) :
    reps k g × R (K := K) (n := n) k ≃ {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k} :=
  Equiv.ofBijective _ (bijective_mulMap hk (existsUnique_reps k g))

theorem coe_rankEquiv {k : ℕ} (hk : k ≤ n) (g : normOneGL K n) (x : reps k g × R (K := K) (n := n) k) :
    ((rankEquiv hk g x : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k}) : Matrix (Fin n) (Fin n) K) =
      (x.2 : Matrix (Fin n) (Fin n) K) * ((x.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem mul_ratMat_mul (y : AdelicGLn.AdelicGL K n) (Z : Matrix (Fin n) (Fin n) K) (γ : GL (Fin n) K)
    (g : normOneGL K n) :
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z * (γ : Matrix (Fin n) (Fin n) K)) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      (y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat Z *
        (((ratOne K n γ * g : normOneGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [ratMat_mul, Subgroup.coe_mul, Units.val_mul, coe_ratOne_matrix]
  simp only [Matrix.mul_assoc]

theorem tsum_rank_eq {k : ℕ} (hk : k ≤ n) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (y : AdelicGLn.AdelicGL K n) (g : normOneGL K n)
    (hs : Summable fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
      ratMat ξ * ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ∑' γ : GL (Fin n) K, (fundamentalDomain (parabolicOne K n k)).indicator (thetaR k Φ y)
        (ratOne K n γ * g) := by
  have hsumR : Summable fun ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k} =>
      Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) :=
    hs.of_norm.comp_injective Subtype.val_injective
  have hP : Summable fun c : reps k g × R (K := K) (n := n) k =>
      Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ((rankEquiv hk g c : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k}) :
          Matrix (Fin n) (Fin n) K) * ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) :=
    hsumR.comp_injective (rankEquiv hk g).injective
  rw [← (rankEquiv hk g).tsum_eq, hP.tsum_prod]
  have hin : ∀ b : reps k g, (∑' c : R (K := K) (n := n) k, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
      ratMat ((rankEquiv hk g (b, c) : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k}) :
        Matrix (Fin n) (Fin n) K) * ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) =
      thetaR k Φ y (ratOne K n (b : GL (Fin n) K) * g) := by
    intro b
    simp only [coe_rankEquiv, thetaR, mul_ratMat_mul]
  rw [tsum_congr hin, tsum_subtype (reps k g) (fun γ => thetaR k Φ y (ratOne K n γ * g))]
  refine tsum_congr fun γ => ?_
  by_cases hγ : γ ∈ reps k g
  · rw [indicator_of_mem hγ, indicator_of_mem
      (show ratOne K n γ * g ∈ fundamentalDomain (parabolicOne K n k) from hγ)]
  · rw [indicator_of_notMem hγ, indicator_of_notMem
      (show ratOne K n γ * g ∉ fundamentalDomain (parabolicOne K n k) from hγ)]

theorem tsum_rank_enorm_eq {k : ℕ} (hk : k ≤ n) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (y : AdelicGLn.AdelicGL K n) (g : normOneGL K n) :
    ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
        ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ =
      ∑' γ : GL (Fin n) K, (fundamentalDomain (parabolicOne K n k)).indicator
        (fun h : normOneGL K n => ∑' Z : R (K := K) (n := n) k,
          ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
            ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ)
        (ratOne K n γ * g) := by
  rw [← (rankEquiv hk g).tsum_eq, ENNReal.tsum_prod']
  set T : normOneGL K n → ℝ≥0∞ := fun h => ∑' Z : R (K := K) (n := n) k,
    ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
      ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ with hT
  have hin : ∀ b : reps k g, (∑' c : R (K := K) (n := n) k, ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
      ratMat ((rankEquiv hk g (b, c) : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k}) :
        Matrix (Fin n) (Fin n) K) * ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ) =
      T (ratOne K n (b : GL (Fin n) K) * g) := by
    intro b
    simp only [hT, coe_rankEquiv, mul_ratMat_mul]
  rw [tsum_congr hin, tsum_subtype (reps k g) (fun γ => T (ratOne K n γ * g))]
  refine tsum_congr fun γ => ?_
  by_cases hγ : γ ∈ reps k g
  · rw [indicator_of_mem hγ, indicator_of_mem
      (show ratOne K n γ * g ∈ fundamentalDomain (parabolicOne K n k) from hγ)]
  · rw [indicator_of_notMem hγ, indicator_of_notMem
      (show ratOne K n γ * g ∉ fundamentalDomain (parabolicOne K n k) from hγ)]

theorem ratMat_mul_unipMatrix {k : ℕ} {Z : Matrix (Fin n) (Fin n) K}
    (hZ : ∀ i j : Fin n, (j : ℕ) < k → Z i j = 0) (X : UPos n k → 𝔸[K]) :
    ratMat Z * unipMatrix X = ratMat Z := by
  rw [unipMatrix, Matrix.mul_add, Matrix.mul_one, add_eq_left]
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [blockEntry_apply]
  split_ifs with h
  · simp [ratMat, hZ i a h.1]
  · rw [mul_zero]

theorem thetaR_unipOne {k : ℕ} (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (y : AdelicGLn.AdelicGL K n)
    (X : UPos n k → 𝔸[K]) (g : normOneGL K n) :
    thetaR k Φ y (unipOne K n k X * g) = thetaR k Φ y g := by
  refine tsum_congr fun Z => ?_
  congr 1
  rw [Subgroup.coe_mul, Units.val_mul, coe_unipOne, coe_unipGL, ← Matrix.mul_assoc,
    Matrix.mul_assoc (y : Matrix (Fin n) (Fin n) 𝔸[K]), ratMat_mul_unipMatrix Z.2.1]

def rightMulR {k : ℕ} (hk : k ≤ n) {p : GL (Fin n) K} (hp : p ∈ parabolic (K := K) (n := n) k) :
    R (K := K) (n := n) k ≃ R (K := K) (n := n) k where
  toFun Z := ⟨(Z : Matrix (Fin n) (Fin n) K) * (p : Matrix (Fin n) (Fin n) K), by
    rw [mem_R_iff hk]
    ext v
    rw [kerM_mul, (mem_R_iff hk).1 Z.2, mulVec_mem_U0_iff hp]⟩
  invFun Z := ⟨(Z : Matrix (Fin n) (Fin n) K) * ((p⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), by
    rw [mem_R_iff hk]
    ext v
    rw [kerM_mul, (mem_R_iff hk).1 Z.2, mulVec_mem_U0_iff (inv_mem hp)]⟩
  left_inv Z := by
    refine Subtype.ext ?_
    simp [Matrix.mul_assoc]
  right_inv Z := by
    refine Subtype.ext ?_
    simp [Matrix.mul_assoc]

theorem thetaR_ratOne {k : ℕ} (hk : k ≤ n) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (y : AdelicGLn.AdelicGL K n) {p : GL (Fin n) K} (hp : p ∈ parabolic (K := K) (n := n) k)
    (g : normOneGL K n) : thetaR k Φ y (ratOne K n p * g) = thetaR k Φ y g := by
  rw [thetaR, thetaR, ← (rightMulR hk hp).tsum_eq (fun Z : R (K := K) (n := n) k =>
    Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
      ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])))]
  refine tsum_congr fun Z => ?_
  show _ = Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
    ratMat ((Z : Matrix (Fin n) (Fin n) K) * (p : Matrix (Fin n) (Fin n) K)) *
      ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
  rw [mul_ratMat_mul]

theorem setIntegral_mul_tsum_rank_eq_zero (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ)
    (hψ : IsCuspidal ψ) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ)
    (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C)
    {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∫ g in fundamentalDomain (rationalGLOne K n), ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hbd
  have hkn' : k ≤ n := hkn.le
  set E := fundamentalDomain (parabolicOne K n k) with hE
  set FΓ := fundamentalDomain (rationalGLOne K n) with hFΓ
  set F : normOneGL K n → ℂ := thetaR k Φ y with hF
  set ψ' : normOneGL K n → ℂ := fun h => ψ (h : AdelicGLn.AdelicGL K n) with hψ'
  set H : normOneGL K n → ℂ := E.indicator (fun h => ψ' h * F h) with hH
  have hψΓ : ∀ (γ : GL (Fin n) K) (g : normOneGL K n), ψ' (ratOne K n γ * g) = ψ' g :=
    fun γ g => hψl γ g

  have hcoe : Continuous fun h : normOneGL K n =>
      ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    Units.continuous_val.comp continuous_subtype_val
  have hψm : Measurable ψ' := (hψc.comp continuous_subtype_val).measurable
  have hFm : Measurable F := by
    refine measurable_tsum_of_summable (fun Z => ?_) (fun h => ?_)
    · exact (hΦ.comp (continuous_const.matrix_mul hcoe)).measurable
    · exact (hsum (h : AdelicGLn.AdelicGL K n)).of_norm.comp_injective Subtype.val_injective
  have hHm : Measurable H := (hψm.mul hFm).indicator (measurableSet_fundamentalDomain _)

  have hpt : ∀ g : normOneGL K n, ψ' g * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
      Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ∑' γ : rationalGLOne K n, H (γ • g) := by
    intro g
    rw [tsum_rank_eq hkn' Φ y g (hsum (g : AdelicGLn.AdelicGL K n)), ← tsum_mul_left,
      ← ratEquiv.tsum_eq]
    refine tsum_congr fun γ => ?_
    simp only [hH, Subgroup.smul_def, coe_ratEquiv, smul_eq_mul]
    by_cases hγ : ratOne K n γ * g ∈ E
    · rw [indicator_of_mem hγ, indicator_of_mem hγ, hψΓ]
    · rw [indicator_of_notMem hγ, indicator_of_notMem hγ, mul_zero]

  have hbound : ∀ g : normOneGL K n, ∑' γ : rationalGLOne K n, ‖H (γ • g)‖ₑ ≤ ENNReal.ofReal C := by
    intro g
    have h1 : ∀ γ : GL (Fin n) K, ‖H (ratOne K n γ * g)‖ₑ ≤ ‖ψ' g‖ₑ *
        E.indicator (fun h : normOneGL K n => ∑' Z : R (K := K) (n := n) k,
          ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
            ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ) (ratOne K n γ * g) := by
      intro γ
      by_cases hγ : ratOne K n γ * g ∈ E
      · rw [hH, indicator_of_mem hγ, indicator_of_mem hγ, enorm_mul, hψΓ]
        gcongr
        exact enorm_tsum_le_tsum_enorm
      · rw [hH, indicator_of_notMem hγ, indicator_of_notMem hγ]
        simp
    calc ∑' γ : rationalGLOne K n, ‖H (γ • g)‖ₑ
        = ∑' γ : GL (Fin n) K, ‖H (ratOne K n γ * g)‖ₑ := by
          rw [← ratEquiv.tsum_eq]
          rfl
      _ ≤ ∑' γ : GL (Fin n) K, ‖ψ' g‖ₑ *
          E.indicator (fun h : normOneGL K n => ∑' Z : R (K := K) (n := n) k,
            ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (Z : Matrix (Fin n) (Fin n) K) *
              ((h : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ) (ratOne K n γ * g) :=
          ENNReal.tsum_le_tsum h1
      _ = ‖ψ' g‖ₑ * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
          ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ := by
          rw [ENNReal.tsum_mul_left, tsum_rank_enorm_eq hkn']
      _ ≤ ‖ψ' g‖ₑ * ∑' ξ : Matrix (Fin n) (Fin n) K,
          ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ₑ :=
          by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ENNReal.ofReal (‖ψ' g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
          ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
            ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum (g : AdelicGLn.AdelicGL K n))]
          simp only [ofReal_norm]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC (g : AdelicGLn.AdelicGL K n) g.2)

  have hFΓfd : IsFundamentalDomain (rationalGLOne K n) FΓ μ := isFundamentalDomain_fundamentalDomain _ μ
  have hFΓfin : μ FΓ < ∞ := by
    have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
    rw [← quotientMeasure_univ μ hFΓfd]
    exact measure_lt_top _ _
  have hlint : ∫⁻ g, ‖H g‖ₑ ∂μ < ∞ := by
    rw [hFΓfd.lintegral_eq_tsum'', ← lintegral_tsum]
    · calc ∫⁻ g in FΓ, ∑' γ : rationalGLOne K n, ‖H (γ • g)‖ₑ ∂μ ≤ ∫⁻ _ in FΓ, ENNReal.ofReal C ∂μ :=
            lintegral_mono fun g => hbound g
        _ = ENNReal.ofReal C * μ FΓ := by rw [setLIntegral_const]
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFΓfin
    · intro γ
      exact (hHm.enorm.comp (measurable_const_mul (γ : normOneGL K n))).aemeasurable.restrict
  have hHint : Integrable H μ := ⟨hHm.aestronglyMeasurable, hlint⟩

  have hunf : ∫ g in FΓ, ∑' γ : rationalGLOne K n, H (γ • g) ∂μ = ∫ g, H g ∂μ := by
    rw [hFΓfd.integral_eq_tsum'' H hHint, integral_tsum]
    · intro γ
      exact (hHm.comp (measurable_const_mul (γ : normOneGL K n))).aestronglyMeasurable.restrict
    · rw [← hFΓfd.lintegral_eq_tsum'' (fun g => ‖H g‖ₑ)]
      exact hlint.ne

  have hint : ∫⁻ g in E, ‖ψ' g * F g‖ₑ ∂μ < ∞ := by
    have : ∫⁻ g in E, ‖ψ' g * F g‖ₑ ∂μ = ∫⁻ g, ‖H g‖ₑ ∂μ := by
      rw [← lintegral_indicator (measurableSet_fundamentalDomain _)]
      refine lintegral_congr fun g => ?_
      rw [hH, enorm_indicator_eq_indicator_enorm]
    rw [this]
    exact hlint
  have hzero : ∫ g in E, ψ' g * F g ∂μ = 0 := by
    refine (hyp (K := K) (n := n) k).setIntegral_mul_eq_zero (μ := μ) hψm hFm ?_ ?_ hint ?_
      (unipMeasure_unipFundamentalDomain_ne_zero k) (unipMeasure_unipFundamentalDomain_ne_top k)
    · intro p hp g
      obtain ⟨p', hp', rfl⟩ := mem_parabolicOne_iff.1 hp
      rw [hψΓ, hF, thetaR_ratOne hkn' Φ y hp']
    · intro X g
      exact thetaR_unipOne Φ y X g
    · intro g
      have := hψ k hk hkn (g : AdelicGLn.AdelicGL K n)
      rw [constantTerm] at this
      simpa [hψ'] using this
  calc ∫ g in FΓ, ψ (g : AdelicGLn.AdelicGL K n) *
        ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = n - k},
          Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ
      = ∫ g in FΓ, ∑' γ : rationalGLOne K n, H (γ • g) ∂μ :=
        setIntegral_congr_fun (measurableSet_fundamentalDomain _) fun g _ => hpt g
    _ = ∫ g, H g ∂μ := hunf
    _ = ∫ g in E, ψ' g * F g ∂μ := integral_indicator (measurableSet_fundamentalDomain _)
    _ = 0 := hzero

end UnfoldGL

end

end GroundTheory.Automorphic.GJGlobal
