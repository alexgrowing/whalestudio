import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

open NumberField Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace UpperTheory.V.Fb

private theorem box {n d : ℕ} (hd : d ≠ 0) {r : Fin (n + 1) → ℝ} (hr : ∀ i, 0 < r i) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h1 : ∀ i, 1 ≤ A * r i ^ d) (h2 : (∏ i, r i) ^ d ≤ B) (i : Fin (n + 1)) :
    r i ≤ B * A ^ (n + 1) ∧ (r i)⁻¹ ≤ B * A ^ (n + 1) := by
  have hL : 1 ≤ B * A ^ (n + 1) := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hA)
  have key : ∀ x : ℝ, x ^ d ≤ B * A ^ (n + 1) → x ≤ B * A ^ (n + 1) := fun x hx =>
    le_of_pow_le_pow_left₀ hd (by positivity) (hx.trans (le_self_pow₀ hL hd))
  refine ⟨key _ ?_, key _ ?_⟩
  · have h3 : 1 ≤ ∏ j : Fin n, A * r (i.succAbove j) ^ d :=
      Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun j _ => h1 _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow] at h3
    rw [Fin.prod_univ_succAbove _ i, mul_pow] at h2
    have h4 := pow_pos (hr i) d
    calc r i ^ d ≤ r i ^ d * (A ^ n * (∏ j : Fin n, r (i.succAbove j)) ^ d) := le_mul_of_one_le_right h4.le h3
      _ = (r i ^ d * (∏ j : Fin n, r (i.succAbove j)) ^ d) * A ^ n := by ring
      _ ≤ B * A ^ (n + 1) := mul_le_mul h2 (pow_le_pow_right₀ hA n.le_succ) (by positivity) (by positivity)
  · rw [inv_pow]
    refine ((inv_le_iff_one_le_mul₀ (pow_pos (hr i) d)).2 (h1 i)).trans ?_
    exact (le_self_pow₀ hA n.succ_ne_zero).trans (le_mul_of_one_le_left (by positivity) hB)

variable {K : Type} [Field K] [NumberField K]

private theorem lastRow {m : ℕ} {ω : Set (AdelicGLn.AdelicGL K (m + 1))} (hω : IsCompact ω)
    (hB : ω ⊆ (adelicBorel (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1)))) :
    ∃ P : ℝ, 0 < P ∧ ∀ b ∈ ω, ∀ (r : Fin (m + 1) → ℝ) (hr : ∀ i, 0 < r i),
      height (b * diagUnits (m + 1) fun i => posIdele (K := K) (r i) (hr i)) (Pi.single (Fin.last m) 1) ≤
        P * r (Fin.last m) ^ Module.finrank ℚ K := by
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul hω
  refine ⟨P, hP, fun b hb r hr => ?_⟩
  obtain ⟨u, hu⟩ := isUnit_apply_self_of_mem_adelicBorel (hB hb) (Fin.last m)
  have e : Pi.single (Fin.last m) 1 ᵥ* b.val = Pi.single (Fin.last m) u.val := by
    rw [single_one_vecMul]
    funext j
    rcases (Fin.le_last j).eq_or_lt with rfl | hj
    · simp [Matrix.row, hu]
    · rw [Pi.single_eq_of_ne hj.ne]
      exact hB hb hj
  have h1 := h b hb _ (hasFiniteContent_single_one (K := K) (Fin.last m))
  rw [e, adelicNorm_single_one, mul_one, adelicNorm_single_units] at h1
  rw [height, Units.val_mul, ← vecMul_vecMul, ratVec_single_one, e, coe_diagUnits, single_vecMul_diagonal,
    ← Units.val_mul, adelicNorm_single_units, map_mul, Positive.val_mul, ideleModule_posIdele]
  exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (hr _).le _)

theorem siegelHeight : SiegelHeight := by
  intro K _ _ n ω hω hB t ht
  cases n with
  | zero => exact ⟨1, 1, fun g γ _ => by rw [Subsingleton.elim (_ * g) g, one_mul, pow_one]⟩
  | succ m =>
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height K (m + 1)
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := UpperTheory.adelicNorm_det_le_height_pow K (m + 1)
  obtain ⟨P, hP, h₃⟩ := lastRow hω hB
  obtain ⟨M, h₄⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
  obtain ⟨p, q, hp, -, h₅⟩ := exists_pos_bounds hω (f := fun b => (ideleModule K (AdelicGLn.det K _ b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det K _)))
    fun b _ => (ideleModule K (AdelicGLn.det K _ b)).2
  set d := Module.finrank ℚ K with hd
  have hs : 0 < min t 1 := lt_min ht one_pos
  set s := (min t 1 ^ m) ^ d with hsd
  have hs0 : 0 < s := by positivity
  set A := max 1 (C₁ * P / s)
  set B := max 1 (C₂ / p)
  set e := 2 * Fintype.card (InfinitePlace K)
  set c := AutomorphicForm.heightConst K (m + 1)
  have hc : 0 ≤ c := zero_le_one.trans AutomorphicForm.one_le_heightConst
  refine ⟨c * (c * M * (B * A ^ (m + 1)) ^ e), (N₂ + N₁ * (m + 1)) * e, ?_⟩
  rintro g γ ⟨b, hb, _, ⟨r, hr, hch, rfl⟩, k, hk, heq⟩
  have hH := AutomorphicForm.one_le_height g
  set H := AutomorphicForm.height g
  have hA : 1 ≤ A * H ^ N₁ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hH)
  have hB' : 1 ≤ B * H ^ N₂ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hH)
  have hx : (Pi.single (Fin.last m) 1 ᵥ* γ.val : Fin (m + 1) → K) ≠ 0 := fun h0 => by
    have := congrArg (fun y => (y ᵥ* (γ⁻¹).val) (Fin.last m)) h0
    simp only [vecMul_vecMul, Units.mul_inv, vecMul_one, zero_vecMul] at this
    simp at this
  have l1 := h₁ g _ hx
  rw [← height_diagonal_mul, heq, height_mul_maxCompact _ hk] at l1
  have l2 : ∀ i, 1 ≤ A * H ^ N₁ * r i ^ d := fun i => by
    have h6 := pow_le_pow_left₀ (mul_pos (pow_pos hs m) (hr _)).le
      (pow_mul_le_of_chain hs.le (min_le_right _ _) (min_le_left _ _) hr hch i) d
    rw [mul_pow] at h6
    calc 1 ≤ C₁ * H ^ N₁ * (P * r (Fin.last m) ^ d) := l1.trans (mul_le_mul_of_nonneg_left (h₃ b hb r hr) (by positivity))
      _ = C₁ * P / s * H ^ N₁ * (s * r (Fin.last m) ^ d) := by field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) h6
          (mul_pos hs0 (pow_pos (hr _) d)).le (zero_le_one.trans hA)
  have l3 : (∏ i, r i) ^ d ≤ B * H ^ N₂ := by
    have h6 := det_mul_mul b (diagUnits (m + 1) fun i => posIdele (K := K) (r i) (hr i)) k
    rw [← heq, map_mul, map_mul, Positive.val_mul, mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩), one_mul,
      ideleModule_det_diagUnits_posIdele r hr, mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one] at h6
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀' hp]
    exact (mul_le_mul_of_nonneg_right (h₅ b hb).1 (pow_nonneg (Finset.prod_pos fun i _ => hr i).le _)).trans
      (h6.symm.le.trans (h₂ g))
  have l4 := CuspidalSpectrum.height_diagUnits_posIdele_le (K := K) hr
    (one_le_mul_of_one_le_of_one_le hB' (one_le_pow₀ hA)) (box Module.finrank_pos.ne' hr hA hB' l2 l3)
  rw [heq]
  refine (AutomorphicForm.height_mul_le _ _).trans ?_
  rw [AutomorphicForm.height_eq_one_of_mem_maxCompact hk, mul_one, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((AutomorphicForm.height_mul_le _ _).trans ?_) hc
  refine (mul_le_mul (mul_le_mul_of_nonneg_left (h₄ b hb) hc) l4 (AutomorphicForm.height_pos _).le
    (mul_nonneg hc ((AutomorphicForm.height_pos b).le.trans (h₄ b hb)))).trans (le_of_eq ?_)
  rw [pow_mul H, pow_add H, pow_mul H, mul_assoc (c * M), ← mul_pow, mul_pow A]
  congr 2
  ring

end UpperTheory.V.Fb
