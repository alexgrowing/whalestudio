import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open GroundTheory.Global GroundTheory.Global.IdeleGroup

private theorem le_of_pow_le' {x B : ℝ} {d : ℕ} (hd : d ≠ 0) (hB : 1 ≤ B) (h : x ^ d ≤ B) : x ≤ B := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans hB
  · exact (le_self_pow₀ h1.le hd).trans h

private theorem two_sided {m : ℕ} {r : Fin (m + 1) → ℝ} {A D : ℝ} (hr : ∀ i, 0 < r i) (hA : 1 ≤ A)
    (hD : 1 ≤ D) (h1 : ∀ i, (r i)⁻¹ ≤ A) (h2 : ∏ i, r i ≤ D) (i : Fin (m + 1)) :
    r i ≤ D * A ^ (m + 1) ∧ (r i)⁻¹ ≤ D * A ^ (m + 1) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  constructor
  · have hQ : 0 < ∏ j ∈ Finset.univ.erase i, r j := Finset.prod_pos fun j _ => hr j
    have e : r i = (∏ j, r j) * ∏ j ∈ Finset.univ.erase i, (r j)⁻¹ := by
      rw [← Finset.mul_prod_erase _ r (Finset.mem_univ i), Finset.prod_inv_distrib,
        mul_inv_cancel_right₀ hQ.ne']
    have h3 : ∏ j ∈ Finset.univ.erase i, (r j)⁻¹ ≤ A ^ (m + 1) := by
      refine (Finset.prod_le_prod (fun j _ => (inv_pos.2 (hr j)).le) fun j _ => h1 j).trans ?_
      rw [Finset.prod_const]
      exact pow_le_pow_right₀ hA ((Finset.card_le_univ _).trans (by simp))
    rw [e]
    exact mul_le_mul h2 h3 (Finset.prod_nonneg fun j _ => (inv_pos.2 (hr j)).le) (by linarith)
  · exact (h1 i).trans ((le_self_pow₀ hA (by omega)).trans
      (le_mul_of_one_le_left (by positivity) hD))

open Reduction in
private theorem last_row {K : Type} [Field K] [NumberField K] {m : ℕ}
    {ω : Set (AdelicGLn.AdelicGL K (m + 1))} (hω : IsCompact ω)
    (hωB : ω ⊆ (adelicBorel (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1)))) :
    ∃ P : ℝ, 0 < P ∧ ∀ b ∈ ω, ∀ (r : Fin (m + 1) → ℝ) (hr : ∀ i, 0 < r i),
      Reduction.height (b * diagUnits (m + 1) fun i => posIdele (K := K) (r i) (hr i))
        (Pi.single (Fin.last m) 1) ≤ P * r (Fin.last m) ^ Module.finrank ℚ K := by
  obtain ⟨P, hP, hle⟩ := exists_adelicNorm_vecMul_le_mul hω
  refine ⟨P, hP, fun b hb r hr => ?_⟩
  have hu := isUnit_apply_self_of_mem_adelicBorel (hωB hb) (Fin.last m)
  have hrow : (Pi.single (Fin.last m) (1 : AdeleRing (𝓞 K) K)) ᵥ* b.val =
      Pi.single (Fin.last m) (hu.unit : AdeleRing (𝓞 K) K) := by
    rw [single_one_vecMul]
    funext j
    rcases (Fin.le_last j).eq_or_lt with rfl | hj
    · simp [Matrix.row]
    · have h0 : b.val (Fin.last m) j = 0 := mem_adelicBorel.1 (hωB hb) hj
      simp [Matrix.row, Pi.single_eq_of_ne hj.ne, h0]
  have h1 := hle b hb _ (hasFiniteContent_single_one (K := K) (Fin.last m))
  rw [hrow, adelicNorm_single_one, mul_one, adelicNorm_single_units] at h1
  rw [Reduction.height, Units.val_mul, ← vecMul_vecMul, ratVec_single_one, hrow, coe_diagUnits,
    single_vecMul_diagonal, ← Units.val_mul, adelicNorm_single_units, map_mul, Positive.val_mul,
    ideleModule_posIdele]
  exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (hr _).le _)

theorem UpperTheory.siegelSet_height_bound :
    UpperTheory.V.Fb.SiegelHeight := by
  intro K _ _ n ω hω hωB t ht
  cases n with
  | zero =>
    refine ⟨1, 0, fun g γ _ => ?_⟩
    rw [show AdelicGLn.diagonal K 0 γ * g = 1 from Units.ext (Subsingleton.elim _ _), height_one]
    simp
  | succ m =>
    obtain ⟨P, hP, hrow⟩ := last_row hω hωB
    obtain ⟨C₁, N₁, hC₁, hvec⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height K (m + 1)
    obtain ⟨C₂, N₂, hC₂, hdet⟩ := UpperTheory.adelicNorm_det_le_height_pow K (m + 1)
    obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
    obtain ⟨B₁, B₂, hB₁, -, hB⟩ := Reduction.exists_pos_bounds hω
      (f := fun b => (ideleModule K (AdelicGLn.det K (m + 1) b) : ℝ))
      (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det K _)))
      (fun b _ => (ideleModule K (AdelicGLn.det K _ b)).2)
    have hd : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
    set s : ℝ := min t 1 with hs
    have hs0 : 0 < s := lt_min ht one_pos
    have hu : 1 ≤ (s ^ m)⁻¹ := (one_le_inv₀ (pow_pos hs0 _)).2 (pow_le_one₀ hs0.le (min_le_right _ _))
    set a₁ : ℝ := max 1 (C₁ * P) with ha₁
    set a₂ : ℝ := max 1 (C₂ / B₁) with ha₂
    have ha₁1 : 1 ≤ a₁ := le_max_left _ _
    have ha₂1 : 1 ≤ a₂ := le_max_left _ _
    set e := 2 * Fintype.card (InfinitePlace K) with he
    set c := heightConst K (m + 1) with hc
    have hc0 : 0 ≤ c := zero_le_one.trans one_le_heightConst
    refine ⟨c * (c * M * (a₂ * ((s ^ m)⁻¹ * a₁) ^ (m + 1)) ^ e), (N₂ + N₁ * (m + 1)) * e, ?_⟩
    rintro g γ ⟨b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, heq⟩
    have hH := one_le_height g
    have hH1 : 1 ≤ AutomorphicForm.height g ^ N₁ := one_le_pow₀ hH
    have hH2 : 1 ≤ AutomorphicForm.height g ^ N₂ := one_le_pow₀ hH
    have hx : (Pi.single (Fin.last m) (1 : K)) ᵥ* γ.val ≠ 0 := fun h0 => by
      have h1 := congrArg (fun y => y ᵥ* (γ⁻¹).val) h0
      simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
        zero_vecMul] at h1
      simpa using congrFun h1 (Fin.last m)
    have h1 := hvec g _ hx
    rw [← Reduction.height_diagonal_mul, heq, Reduction.height_mul_maxCompact _ hk] at h1
    have hA : 1 ≤ a₁ * AutomorphicForm.height g ^ N₁ := one_le_mul_of_one_le_of_one_le ha₁1 hH1
    have hD : 1 ≤ a₂ * AutomorphicForm.height g ^ N₂ := one_le_mul_of_one_le_of_one_le ha₂1 hH2
    have hl : (r (Fin.last m))⁻¹ ≤ a₁ * AutomorphicForm.height g ^ N₁ := by
      refine le_of_pow_le' hd hA ?_
      rw [inv_pow, inv_le_iff_one_le_mul₀ (pow_pos (hr _) _)]
      refine h1.trans ((mul_le_mul_of_nonneg_left (hrow b hb r hr) (by positivity)).trans ?_)
      have := pow_pos (hr (Fin.last m)) (Module.finrank ℚ K)
      calc _ = C₁ * P * (AutomorphicForm.height g ^ N₁ * r (Fin.last m) ^ Module.finrank ℚ K) := by ring
        _ ≤ a₁ * (AutomorphicForm.height g ^ N₁ * r (Fin.last m) ^ Module.finrank ℚ K) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = _ := by ring
    have hall : ∀ i, (r i)⁻¹ ≤ (s ^ m)⁻¹ * (a₁ * AutomorphicForm.height g ^ N₁) := fun i => by
      have h2 := Reduction.pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hr hratio i
      refine (inv_anti₀ (mul_pos (pow_pos hs0 _) (hr _)) h2).trans ?_
      rw [mul_inv]
      exact mul_le_mul_of_nonneg_left hl (by linarith)
    have hX : ∏ i, r i ≤ a₂ * AutomorphicForm.height g ^ N₂ := by
      refine le_of_pow_le' hd hD ?_
      have h2 := Reduction.det_mul_mul b
        (Reduction.diagUnits (m + 1) fun i => Reduction.posIdele (K := K) (r i) (hr i)) k
      rw [← heq, Reduction.ideleModule_det_diagUnits_posIdele r hr,
        Reduction.mem_normOneGL.1 (Reduction.maxCompact_le_normOneGL hk), mul_one, map_mul, map_mul,
        Positive.val_mul, Reduction.mem_normOneGL.1 (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩),
        one_mul] at h2
      have hX0 : 0 ≤ (∏ i, r i) ^ Module.finrank ℚ K :=
        pow_nonneg (Finset.prod_nonneg fun i _ => (hr i).le) _
      have h3 : B₁ * (∏ i, r i) ^ Module.finrank ℚ K ≤ C₂ * AutomorphicForm.height g ^ N₂ :=
        (mul_le_mul_of_nonneg_right (hB b hb).1 hX0).trans (h2 ▸ hdet g)
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right 1 (C₂ / B₁)) (by linarith))
      rw [div_mul_eq_mul_div, le_div_iff₀' hB₁]
      exact h3
    have hA' := one_le_mul_of_one_le_of_one_le hu hA
    have ha := CuspidalSpectrum.height_diagUnits_posIdele_le (K := K) hr
      (one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hA')) (two_sided hr hA' hD hall hX)
    have hM0 : 0 ≤ M := (height_pos b).le.trans (hM b hb)
    rw [heq]
    refine (height_mul_le _ _).trans ?_
    rw [height_eq_one_of_mem_maxCompact hk, mul_one, mul_assoc c]
    refine mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans ?_) hc0
    refine (mul_le_mul (mul_le_mul_of_nonneg_left (hM b hb) hc0) ha (height_pos _).le
      (mul_nonneg hc0 hM0)).trans (le_of_eq ?_)
    rw [← he, mul_assoc (c * M), pow_mul (AutomorphicForm.height g), ← mul_pow,
      pow_add (AutomorphicForm.height g), pow_mul (AutomorphicForm.height g)]
    congr 2
    rw [← mul_assoc ((s ^ m)⁻¹), mul_pow _ (AutomorphicForm.height g ^ N₁)]
    ring
