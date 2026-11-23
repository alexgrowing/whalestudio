import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeNormInfCModuleSectionMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap ContDiff
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

section Majorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_dilate_le (f : 𝓢(E, ℝ)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (a • y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a • x)‖ := by
  have hg : (fun y ↦ f (a • y)) = f ∘ (a • ContinuousLinearMap.id ℝ E) := rfl
  have hle : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg ha0]
    exact mul_le_one₀ ha1 (norm_nonneg _) ContinuousLinearMap.norm_id_le
  rw [hg, ContinuousLinearMap.iteratedFDeriv_comp_right _ (f.smooth ⊤) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hle

theorem exists_schwartz_majorant [FiniteDimensional ℝ E] (φ : 𝓢(E, ℂ)) :
    ∃ Φ : 𝓢(E, ℂ), ∃ r : E → ℝ, (∀ y, Φ y = (r y : ℂ)) ∧ ∀ y, ‖φ y‖ ≤ r y := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, by norm_num⟩
  let χ : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ b.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ b.le_one
  have hχb : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦
    b.one_of_mem_closedBall (by simpa [b] using hy)
  have hAex : ∀ m : ℕ, ∃ A : ℝ, ∀ y, (1 + ‖y‖) ^ m * ‖φ y‖ ≤ A := fun m ↦
    ⟨_, fun y ↦ by
      simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, 0)) le_rfl le_rfl
        φ y⟩
  choose A hA using hAex
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦
    (by positivity : 0 ≤ (1 + ‖(0 : E)‖) ^ m * ‖φ 0‖).trans (hA m 0)
  let c : ℕ → ℝ := fun k ↦ ⨅ m : ℕ, A m / ((2 : ℝ) ^ k) ^ m
  have hbdd : ∀ k : ℕ, BddBelow (Set.range fun m : ℕ ↦ A m / ((2 : ℝ) ^ k) ^ m) := fun k ↦
    ⟨0, by rintro _ ⟨m, rfl⟩; exact div_nonneg (hA0 m) (by positivity)⟩
  have hc0 : ∀ k, 0 ≤ c k := fun k ↦ le_ciInf fun m ↦ div_nonneg (hA0 m) (by positivity)
  have hcle : ∀ k m, c k ≤ A m / ((2 : ℝ) ^ k) ^ m := fun k m ↦ ciInf_le (hbdd k) m
  have hsum : ∀ m : ℕ, Summable fun k : ℕ ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m := by
    intro m
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hc0 k) (by positivity)) (fun k ↦ ?_)
      (summable_geometric_two.mul_left (A (m + 1) * 2 ^ m))
    have e1 : ((2 : ℝ) ^ (k + 1)) ^ m = ((2 : ℝ) ^ k) ^ m * 2 ^ m := by
      rw [pow_succ, mul_pow]
    have e2 : ((2 : ℝ) ^ k) ^ (m + 1) = ((2 : ℝ) ^ k) ^ m * 2 ^ k := by rw [pow_succ]
    calc c k * ((2 : ℝ) ^ (k + 1)) ^ m
        ≤ A (m + 1) / ((2 : ℝ) ^ k) ^ (m + 1) * ((2 : ℝ) ^ (k + 1)) ^ m := by
          gcongr
          exact hcle k (m + 1)
      _ = A (m + 1) * 2 ^ m * (1 / 2) ^ k := by
          rw [e1, e2, one_div, inv_pow]
          field_simp
  let a : ℕ → ℝ := fun k ↦ ((2 : ℝ) ^ (k + 1))⁻¹
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by positivity
  have ha1 : ∀ k, a k ≤ 1 := fun k ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  let f : ℕ → E → ℝ := fun k y ↦ c k * χ (a k • y)
  have hfsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k ↦
    contDiff_const.mul ((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id))
  choose D hD using fun (m n : ℕ) ↦ χ.decay' m n
  have hfd : ∀ (k m n : ℕ) (x : E),
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
    intro k m n x
    have e1 : iteratedFDeriv ℝ n (f k) x =
        c k • iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x :=
      iteratedFDeriv_const_smul_apply (a := c k) (f := fun y ↦ χ (a k • y))
        (((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id)).contDiffAt.of_le
          (by exact_mod_cast le_top))
    have e2 : ‖x‖ = (2 : ℝ) ^ (k + 1) * ‖a k • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), ← mul_assoc, mul_inv_cancel₀ (by positivity),
        one_mul]
    rw [e1, norm_smul, Real.norm_of_nonneg (hc0 k)]
    calc ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x‖)
        ≤ ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          have := norm_iteratedFDeriv_dilate_le χ (ha0 k) (ha1 k) n x
          have := hc0 k
          gcongr
      _ = c k * ((2 : ℝ) ^ (k + 1)) ^ m *
            (‖a k • x‖ ^ m * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          rw [e2, mul_pow]
          ring
      _ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
          exact mul_le_mul_of_nonneg_left (hD m n (a k • x))
            (mul_nonneg (hc0 k) (by positivity))
  have hfv : ∀ (n k : ℕ) (x : E), ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * D 0 n := by
    intro n k x
    simpa using hfd k 0 n x
  have hsv : ∀ n : ℕ, Summable fun k ↦ c k * D 0 n := fun n ↦ by
    simpa using (hsum 0).mul_right (D 0 n)
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ ∑' k, f k y :=
    contDiff_tsum (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n) fun n k x _ ↦ hfv n k x
  let Φr : 𝓢(E, ℝ) :=
    { toFun := fun y ↦ ∑' k, f k y
      smooth' := hsmooth
      decay' := by
        intro m n
        refine ⟨(∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n, fun x ↦ ?_⟩
        rw [iteratedFDeriv_tsum_apply (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n)
          (fun n k x _ ↦ hfv n k x) (by exact_mod_cast le_top) x]
        have hs1 : Summable fun k ↦ ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hfv n k x) (hsv n)
        have hs2 : Summable fun k ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
          (hsum m).mul_right _
        calc ‖x‖ ^ m * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ m * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hs1
          _ = ∑' k, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ ∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
              (hs1.mul_left _).tsum_le_tsum (fun k ↦ hfd k m n x) hs2
          _ = (∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n := tsum_mul_right }
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM Φr, Φr, fun y ↦ rfl, fun y ↦ ?_⟩
  have hf0 : ∀ k, 0 ≤ f k y := fun k ↦ mul_nonneg (hc0 k) (hχ0 _)
  have hfs : Summable fun k ↦ f k y := by
    refine Summable.of_nonneg_of_le hf0 (fun k ↦ ?_) (by simpa using hsum 0)
    exact mul_le_of_le_one_right (hc0 k) (hχ1 _)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 + ‖y‖) (y := (2 : ℝ))
    (by linarith [norm_nonneg y]) (by norm_num)
  have h1 : ‖φ y‖ ≤ c k := by
    refine le_ciInf fun m ↦ ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hA m y)
    gcongr
  have h2 : f k y = c k := by
    have : χ (a k • y) = 1 := by
      refine hχb _ ?_
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), inv_mul_le_iff₀ (by positivity), mul_one]
      linarith
    simp only [f, this, mul_one]
  calc ‖φ y‖ ≤ f k y := h2 ▸ h1
    _ ≤ ∑' k, f k y := hfs.le_tsum k fun j _ ↦ hf0 j

end Majorant

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

variable {K : Type _} [Field K] [NumberField K]

noncomputable def contragredient (h : GL (Fin 2) 𝔸[K]) : GL (Fin 2) 𝔸[K] :=
  ⟨((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ,
    (h : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩

end GlobalTheory.CompanionTheory.EisRk1
