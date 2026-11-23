import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableBoundedMulWeightFive
open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.ParsC

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC.Theta

def Llin : V2 →ₗ[ℝ] M23 × V2 where
  toFun y := (col 0 y, 0)
  map_add' a b := by
    ext i j <;> first
      | (fin_cases i <;> fin_cases j <;> simp [col])
      | simp
  map_smul' c a := by
    ext i j <;> first
      | (fin_cases i <;> fin_cases j <;> simp [col])
      | simp

def L : V2 →L[ℝ] M23 × V2 := LinearMap.toContinuousLinearMap Llin

lemma L_apply (y : V2) : L y = (col 0 y, 0) := rfl

lemma col_split (κ : M22) (y : V2) (q : V2) : (col κ y, q) = L y + (col κ 0, q) := by
  rw [L_apply]
  ext i j <;> first
    | (fin_cases i <;> fin_cases j <;> simp [col])
    | simp

lemma norm_le_col_left (κ : M22) (y : V2) : ‖κ‖ ≤ ‖col κ y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := (norm_le_pi_norm (col κ y i) (Fin.castSucc j))
  have h' := norm_le_pi_norm (col κ y) i
  refine le_trans (le_of_eq ?_) (h.trans h')
  fin_cases i <;> fin_cases j <;> simp [col]

lemma norm_le_col_right (κ : M22) (y : V2) : ‖y‖ ≤ ‖col κ y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := (norm_le_pi_norm (col κ y i) 2)
  have h' := norm_le_pi_norm (col κ y) i
  refine le_trans (le_of_eq ?_) (h.trans h')
  fin_cases i <;> simp [col]

lemma weight_le (κ : M22) (y q : V2) (N i : ℕ) :
    (1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i * (1 + ‖y‖) ^ 5 ≤ (1 + ‖((col κ y, q) : M23 × V2)‖) ^ (N + i + 5) := by
  set x : M23 × V2 := (col κ y, q)
  have h1 : ‖κ‖ ≤ ‖x‖ := (norm_le_col_left κ y).trans (norm_fst_le x)
  have h2 : ‖y‖ ≤ ‖x‖ := (norm_le_col_right κ y).trans (norm_fst_le x)
  have h3 : ‖q‖ ≤ ‖x‖ := norm_snd_le x
  rw [pow_add, pow_add]
  have a1 : (1 + ‖κ‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) _
  have a2 : (1 + ‖q‖) ^ i ≤ (1 + ‖x‖) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) _
  have a3 : (1 + ‖y‖) ^ 5 ≤ (1 + ‖x‖) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) _
  gcongr

theorem decay : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] (Ψ : SchwartzMap (M23 × V2) F) (N i : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (κ : M22) (q : V2),
    ContDiff ℝ 2 (fun y : V2 => Ψ (col κ y, q)) ∧ ∀ l ≤ 2, ∀ y : V2,
      ‖iteratedFDeriv ℝ l (fun y : V2 => Ψ (col κ y, q)) y‖ ≤ K / ((1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i) * w5 y := by
  intro F _ _ _ _ _ Ψ N i
  set m : ℕ × ℕ := (N + i + 5, 2) with hm
  set S : ℝ := 2 ^ m.1 * ((Finset.Iic m).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) Ψ with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; exact mul_nonneg (by positivity) (apply_nonneg _ _)
  set c : ℝ := 1 + ‖L‖ with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith [norm_nonneg L]
  refine ⟨c ^ 2 * S, by positivity, fun κ q => ?_⟩
  have hfun : (fun y : V2 => Ψ (col κ y, q)) = (fun x => Ψ (x + (col κ 0, q))) ∘ L := by
    funext y
    simp only [Function.comp, col_split κ y q]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Ψ (x + ((col κ 0, q) : M23 × V2))) :=
    (Ψ.smooth ⊤).comp (contDiff_id.add contDiff_const)
  refine ⟨?_, fun l hl y => ?_⟩
  · rw [hfun]
    have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.2 le_top
    exact (hg.of_le h2).comp L.contDiff
  · set x : M23 × V2 := (col κ y, q) with hx
    have hiter : iteratedFDeriv ℝ l (fun y : V2 => Ψ (col κ y, q)) y =
        (iteratedFDeriv ℝ l Ψ x).compContinuousLinearMap fun _ => L := by
      rw [hfun, L.iteratedFDeriv_comp_right hg y (i := l) (by exact_mod_cast le_top),
        iteratedFDeriv_comp_add_right, ← col_split]
    have hnorm : ‖iteratedFDeriv ℝ l (fun y : V2 => Ψ (col κ y, q)) y‖ ≤ c ^ 2 * ‖iteratedFDeriv ℝ l Ψ x‖ := by
      rw [hiter]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖L‖ ^ l ≤ c ^ l := pow_le_pow_left₀ (norm_nonneg _) (by rw [hc]; linarith) _
        _ ≤ c ^ 2 := pow_le_pow_right₀ hc1 hl
    have hsw : (1 + ‖x‖) ^ (N + i + 5) * ‖iteratedFDeriv ℝ l Ψ x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := m) le_rfl hl Ψ x
    have hw := weight_le κ y q N i
    have hA : 0 < (1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i := by positivity
    have hC : 0 < (1 + ‖y‖) ^ 5 := by positivity
    have hfin : ‖iteratedFDeriv ℝ l Ψ x‖ * ((1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i * (1 + ‖y‖) ^ 5) ≤ S := by
      refine le_trans ?_ hsw
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    have hgoal : c ^ 2 * S / ((1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i) * w5 y =
        c ^ 2 * (S / ((1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i * (1 + ‖y‖) ^ 5)) := by
      unfold w5
      field_simp
    rw [hgoal]
    refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [le_div_iff₀ (by positivity)]
    exact hfin

end GlobalTheory.CompanionTheory.ParsC.Theta
