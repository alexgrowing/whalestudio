import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularFormStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.EisT
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped Pointwise

theorem decomp_of_congr_one (M q : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) (hq : q.Prime) (hqM : (M : ℤ) ∣ (q : ℤ) - 1)
    (hdet : B.det = q) (h0 : (M : ℤ) ∣ B 0 0 - 1) (h1 : (M : ℤ) ∣ B 1 0) :
    ∃ e : SL(2, ℤ), e ∈ Gamma M ∧ ∃ b : ℤ,
      B = mat e * (if (q : ℤ) ∣ B 0 0 ∧ (q : ℤ) ∣ B 1 0 then !![(q : ℤ), b; 0, 1] else !![1, b; 0, (q : ℤ)]) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [Matrix.det_fin_two] at hdet
  have aux : ∀ p t : ℤ, IsCoprime p t → (M : ℤ) ∣ p - 1 → (M : ℤ) ∣ t →
      ∃ e : SL(2, ℤ), e ∈ Gamma M ∧ e 0 0 = p ∧ e 1 0 = t := by
    rintro p t ⟨α, β, h⟩ ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨⟨!![p, β * (p - 1); t, α + β * t], by rw [Matrix.det_fin_two_of]; linear_combination h⟩, ?_, rfl, rfl⟩
    have hp : (p : ZMod M) = 1 := by
      rw [show p = 1 + M * x by linarith]; simp
    have ht : (t : ZMod M) = 0 := by rw [hy]; simp
    have hα : (α : ZMod M) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod M)) h
      simpa [hp, ht] using this
    refine Gamma_mem.2 ?_
    simp [hp, ht, hα]
  split_ifs with h
  · obtain ⟨⟨p, hp⟩, ⟨t, ht⟩⟩ := h
    have hc : B 1 1 * p + (-B 0 1) * t = 1 := by
      apply mul_left_cancel₀ hq0
      rw [hp, ht] at hdet
      linear_combination hdet
    obtain ⟨e, he, e0, e1⟩ := aux p t ⟨_, _, hc⟩
      (by rw [show p - 1 = (B 0 0 - 1) - ((q : ℤ) - 1) * p by rw [hp]; ring]
          exact dvd_sub h0 (hqM.mul_right _))
      (by rw [show t = B 1 0 - ((q : ℤ) - 1) * t by rw [ht]; ring]
          exact dvd_sub h1 (hqM.mul_right _))
    have hd : e 0 0 * e 1 1 - e 0 1 * e 1 0 = 1 := by
      have := e.2; rwa [Matrix.det_fin_two] at this
    rw [e0, e1] at hd
    refine ⟨e, he, e 1 1 * B 0 1 - e 0 1 * B 1 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e0, e1]
    · rw [hp]; ring
    · linear_combination (-B 0 1) * hd - e 0 1 * hc + 2 * e 0 1 * hc
    · rw [ht]; ring
    · linear_combination (-B 1 1) * hd + e 1 1 * hc
  · have hc : IsCoprime (B 0 0) (B 1 0) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hg : ((Int.gcd (B 0 0) (B 1 0) : ℕ) : ℤ) ∣ (q : ℤ) := by
        rw [← hdet]
        exact dvd_sub ((Int.gcd_dvd_left ..).mul_right _) ((Int.gcd_dvd_right ..).mul_left _)
      rcases (Nat.dvd_prime hq).1 (by exact_mod_cast hg) with h2 | h2
      · exact h2
      · exact absurd ⟨h2 ▸ Int.gcd_dvd_left .., h2 ▸ Int.gcd_dvd_right ..⟩ h
    obtain ⟨e, he, e0, e1⟩ := aux _ _ hc h0 h1
    have hd : e 0 0 * e 1 1 - e 0 1 * e 1 0 = 1 := by
      have := e.2; rwa [Matrix.det_fin_two] at this
    rw [e0, e1] at hd
    refine ⟨e, he, e 1 1 * B 0 1 - e 0 1 * B 1 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e0, e1]
    · linear_combination (-B 0 1) * hd + e 0 1 * hdet
    · linear_combination (-B 1 1) * hd + e 1 1 * hdet

theorem dvd_col_mul (n : ℤ) (C A : Matrix (Fin 2) (Fin 2) ℤ) (h : n ∣ A 0 0 ∧ n ∣ A 1 0) :
    n ∣ (C * A) 0 0 ∧ n ∣ (C * A) 1 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨dvd_add (h.1.mul_left _) (h.2.mul_left _), dvd_add (h.1.mul_left _) (h.2.mul_left _)⟩

theorem dvd_col_SL_mul (n : ℤ) (P : SL(2, ℤ)) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (n ∣ (mat P * A) 0 0 ∧ n ∣ (mat P * A) 1 0) ↔ (n ∣ A 0 0 ∧ n ∣ A 1 0) := by
  refine ⟨fun h => ?_, dvd_col_mul n _ _⟩
  have := dvd_col_mul n (mat P⁻¹) _ h
  rwa [← Matrix.mul_assoc, mat, mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at this

theorem decomp_of_congr : ∀ (M q : ℕ) (P : SL(2, ℤ)) (A : Matrix (Fin 2) (Fin 2) ℤ), 0 < M → q.Prime → (M : ℤ) ∣ (q : ℤ) - 1 → A.det = q →
  (∀ i j, (M : ℤ) ∣ A i j - mat P i j) → ∃ e : SL(2, ℤ), e ∈ CongruenceSubgroup.Gamma M ∧ ∃ b : ℤ,
    A = mat P * mat e * (if (q : ℤ) ∣ A 0 0 ∧ (q : ℤ) ∣ A 1 0 then !![(q : ℤ), b; 0, 1] else !![1, b; 0, (q : ℤ)]) := by
  intro M q P A _ hq hqM hdet hA
  have hPP : mat P⁻¹ * mat P = 1 := by
    rw [mat, mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hPP' : mat P * mat P⁻¹ = 1 := by
    rw [mat, mat, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h := dvd_col_mul M (mat P⁻¹) (A - mat P) ⟨hA 0 0, hA 1 0⟩
  rw [Matrix.mul_sub, hPP] at h
  obtain ⟨e, he, b, hb⟩ := decomp_of_congr_one M q (mat P⁻¹ * A) hq hqM
    (by rw [Matrix.det_mul, hdet, (P⁻¹).2, one_mul]) (by simpa using h.1) (by simpa using h.2)
  refine ⟨e, he, b, ?_⟩
  simp only [dvd_col_SL_mul] at hb
  rw [Matrix.mul_assoc, ← hb, ← Matrix.mul_assoc, hPP', Matrix.one_mul]

theorem card_dvd_col_eq_one : ∀ (q : ℕ) (σ γ : SL(2, ℤ)), q.Prime →
  (Finset.univ.filter fun i : Fin (q + 1) => (q : ℤ) ∣ (tqFam q σ i * mat γ) 0 0 ∧ (q : ℤ) ∣ (tqFam q σ i * mat γ) 1 0).card = 1 := by
  intro q σ γ hq
  haveI : Fact q.Prime := ⟨hq⟩
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hlt : ∀ i : Fin (q + 1), (i : ℕ) < q → (((q : ℤ) ∣ (tqFam q σ i * mat γ) 0 0 ∧
      (q : ℤ) ∣ (tqFam q σ i * mat γ) 1 0) ↔ ((γ 0 0 : ℤ) : ZMod q) + ((i : ℕ) : ZMod q) * ((γ 1 0 : ℤ) : ZMod q) = 0) := by
    intro i hi
    have : ((γ 0 0 : ℤ) : ZMod q) + ((i : ℕ) : ZMod q) * ((γ 1 0 : ℤ) : ZMod q)
        = ((γ 0 0 + (i : ℕ) * γ 1 0 : ℤ) : ZMod q) := by push_cast; rfl
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [tqFam, hi, Matrix.mul_apply, Fin.sum_univ_two]
  have hge : ∀ i : Fin (q + 1), ¬ (i : ℕ) < q → (((q : ℤ) ∣ (tqFam q σ i * mat γ) 0 0 ∧
      (q : ℤ) ∣ (tqFam q σ i * mat γ) 1 0) ↔ ((γ 1 0 : ℤ) : ZMod q) = 0) := by
    intro i hi
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [tqFam, hi, if_false, Matrix.mul_assoc, dvd_col_SL_mul]
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Finset.card_eq_one]
  by_cases hc : ((γ 1 0 : ℤ) : ZMod q) = 0
  · refine ⟨Fin.last q, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hi : (i : ℕ) < q
    · rw [hlt i hi, hc, mul_zero, add_zero]
      refine ⟨fun ha => ?_, fun h => by rw [h] at hi; simp at hi⟩
      have := congrArg (fun z : ℤ => (z : ZMod q)) hd
      simp [ha, hc] at this
    · rw [hge i hi]
      refine ⟨fun _ => Fin.ext ?_, fun _ => hc⟩
      have := i.2
      simp only [Fin.val_last]; omega
  · set x : ZMod q := -((γ 0 0 : ℤ) : ZMod q) / ((γ 1 0 : ℤ) : ZMod q) with hx
    have hxl : x.val < q := ZMod.val_lt x
    refine ⟨⟨x.val, by omega⟩, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hi : (i : ℕ) < q
    · rw [hlt i hi]
      constructor
      · intro h
        apply Fin.ext
        have : ((i : ℕ) : ZMod q) = x := by
          rw [hx, eq_div_iff hc]; linear_combination h
        simp only [← this, ZMod.val_cast_of_lt hi]
      · rintro rfl
        simp only [ZMod.natCast_val, ZMod.cast_id', id]
        rw [hx, div_mul_cancel₀ _ hc]; ring
    · rw [hge i hi]
      refine ⟨fun h => absurd h hc, fun h => absurd (h ▸ hxl) hi⟩

theorem tendsto_slash_upper : ∀ (k : ℤ) (F : ℍ → ℂ) (c : ℂ) (g b d : ℤ), 0 < g → 0 < d → Tendsto F atImInfty (𝓝 c) →
  Tendsto (F ∣[k] toGL !![g, b; 0, d]) atImInfty (𝓝 (((g * d : ℤ) : ℂ) ^ (k - 1) * ((d : ℤ) : ℂ) ^ (-k) * c)) := by
  intro k F c g b d hg hd hF
  have hdet : (!![g, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    simp [Matrix.det_fin_two_of, hg.ne', hd.ne']
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set β := toGL !![g, b; 0, d] with hβ
  have hv : ∀ i j, (β : Matrix (Fin 2) (Fin 2) ℝ) i j = ((!![g, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := by
    intro i j; simp only [hβ, toGL, hdet, dif_neg, not_false_eq_true]; rfl
  have hD : β.det.val = (g : ℝ) * d := by
    simp [Matrix.det_fin_two, hv]
  have hpos : 0 < β.det.val := by rw [hD]; positivity
  have hden : ∀ τ : ℍ, denom β τ = (d : ℂ) := fun τ => by simp [denom, hv]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hmap : Tendsto (fun τ : ℍ => β • τ) atImInfty atImInfty := by
    rw [atImInfty, tendsto_comap_iff]
    refine (him.const_mul_atTop (div_pos hg' hd')).congr (fun τ => ?_)
    simp only [Function.comp, UpperHalfPlane.im_smul_eq_div_normSq, hden, hD, abs_of_pos (mul_pos hg' hd'),
      Complex.normSq_intCast]
    field_simp
  refine (((hF.comp hmap).const_mul (((g * d : ℤ) : ℂ) ^ (k - 1) * ((d : ℤ) : ℂ) ^ (-k)))).congr (fun τ => ?_)
  rw [ModularForm.slash_apply, hden, hD, abs_of_pos (mul_pos hg' hd'), UpperHalfPlane.σ, if_pos hpos]
  simp
  ring

theorem lev_finiteIndex (N l : ℕ) [NeZero N] [NeZero l] : (Lev N l).FiniteIndex := by
  unfold Lev; infer_instance

theorem tendsto_slash_valueAtInfty (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : 0 < l) (f : ModularForm (Lev N l) k)
    (γ : SL(2, ℤ)) :
    Tendsto (⇑f ∣[k] γ) atImInfty (𝓝 (valueAtInfty (⇑f ∣[k] γ))) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI := lev_finiteIndex N l
  have : ((ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • (Lev N l : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Lev N l : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  obtain ⟨c, hc, hO⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.translate f (γ : GL (Fin 2) ℝ))
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have h0 : Tendsto (fun τ : ℍ => Real.exp (-c * τ.im)) atImInfty (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (him.const_mul_atTop_of_neg (by linarith))
  have := hO.trans_tendsto h0
  simp only [ModularForm.coe_translate] at this
  have h2 := this.add_const (valueAtInfty (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))
  simpa [ModularForm.SL_slash] using h2

theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  simp [toGL, hA, hB, hAB, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = (γ : GL (Fin 2) ℝ) := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  ext i j
  simp [toGL, h]

theorem gamma_le_lev (N l : ℕ) : Gamma (N * l) ≤ Lev N l := by
  intro g hg
  rw [Gamma_mem] at hg
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have cN : ∀ (x : ℤ) (y : ℤ), (x : ZMod (N * l)) = y → (x : ZMod N) = y := fun x y h => by
    simpa using congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h
  have cl : ∀ (x : ℤ) (y : ℤ), (x : ZMod (N * l)) = y → (x : ZMod l) = y := fun x y h => by
    simpa using congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) h
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    exact ⟨by simpa using cN _ 1 (by simpa using h1), by simpa using cN _ 1 (by simpa using h4),
      by simpa using cN _ 0 (by simpa using h3)⟩
  · rw [Gamma0_mem]; simpa using cl _ 0 (by simpa using h3)

theorem slash_lev (N l : ℕ) (k : ℤ) (f : ModularForm (Lev N l) k) (u : SL(2, ℤ)) (hu : u ∈ Lev N l) :
    (⇑f) ∣[k] u = ⇑f := by
  have : ((u : GL (Fin 2) ℝ)) ∈ (Lev N l : Subgroup (GL (Fin 2) ℝ)) := Subgroup.mem_map_of_mem _ hu
  exact SlashInvariantFormClass.slash_action_eq f _ this

theorem slash_decomp (N l : ℕ) (k : ℤ) (q : ℕ) (hq : q.Prime) (hM : 0 < N * l)
    (hqM : ((N * l : ℕ) : ℤ) ∣ (q : ℤ) - 1)
    (f : ModularForm (Lev N l) k) (δ : Matrix (Fin 2) (Fin 2) ℤ) (u : SL(2, ℤ)) (hu : u ∈ Lev N l)
    (hdet : δ.det = q) (hδ : ∀ i j, ((N * l : ℕ) : ℤ) ∣ δ i j - mat u i j) (γ : SL(2, ℤ)) :
    ∃ b : ℤ, (⇑f ∣[k] toGL δ) ∣[k] γ = (⇑f ∣[k] γ) ∣[k] toGL (if (q : ℤ) ∣ (δ * mat γ) 0 0 ∧
      (q : ℤ) ∣ (δ * mat γ) 1 0 then !![(q : ℤ), b; 0, 1] else !![1, b; 0, (q : ℤ)]) := by
  obtain ⟨e, he, b, hA⟩ := decomp_of_congr (N * l) q (u * γ) (δ * mat γ) hM hq hqM
    (by simp [Matrix.det_mul, hdet, mat]) (by
      intro i j
      have h0 : δ * mat γ - mat (u * γ) = (δ - mat u) * mat γ := by
        simp [mat, Matrix.sub_mul]
      have h1 := congrFun (congrFun h0 i) j
      rw [Matrix.sub_apply] at h1
      rw [h1, Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left (by simpa using hδ i 0) _)
        (dvd_mul_of_dvd_left (by simpa using hδ i 1) _))
  refine ⟨b, ?_⟩
  set β := (if (q : ℤ) ∣ (δ * mat γ) 0 0 ∧ (q : ℤ) ∣ (δ * mat γ) 1 0 then !![(q : ℤ), b; 0, 1]
    else !![1, b; 0, (q : ℤ)]) with hβ
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hβdet : β.det ≠ 0 := by
    rw [hβ]; split_ifs <;> simp [Matrix.det_fin_two_of, hq.ne_zero]
  have hδdet : δ.det ≠ 0 := by rw [hdet]; exact hq0
  have hSL : ∀ g : SL(2, ℤ), (mat g).det ≠ 0 := fun g => by simp [mat]
  have key : toGL δ * (γ : GL (Fin 2) ℝ) = ((u * γ * e : SL(2, ℤ)) : GL (Fin 2) ℝ) * toGL β := by
    rw [← toGL_mat γ, ← toGL_mul _ _ hδdet (hSL γ), hA, ← toGL_mat, ← toGL_mul _ _ (hSL _) hβdet]
    congr 2
  have hc : γ * e * γ⁻¹ ∈ Lev N l := gamma_le_lev N l ((Gamma_normal (N * l)).conj_mem e he γ)
  have h2 : (⇑f) ∣[k] (u * γ * e) = (⇑f) ∣[k] γ := by
    have : u * γ * e = u * (γ * e * γ⁻¹) * γ := by group
    rw [this, SlashAction.slash_mul, SlashAction.slash_mul, slash_lev N l k f u hu,
      slash_lev N l k f _ hc]
  rw [ModularForm.SL_slash, ← SlashAction.slash_mul, key, SlashAction.slash_mul, ← ModularForm.SL_slash, h2]

theorem T_zpow_mem_lev (N l : ℕ) (n : ℤ) : ModularGroup.T ^ n ∈ Lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
  · rw [Gamma0_mem]; simp [ModularGroup.coe_T_zpow]

theorem diam_mem_lev (N l q : ℕ) (hqN : (N : ℤ) ∣ (q : ℤ) - 1) (σ : SL(2, ℤ)) (h : IsDiam N l (q : ZMod N) σ) :
    σ ∈ Lev N l := by
  obtain ⟨h1, h2⟩ := h
  rw [Gamma0_mem] at h1
  have hq1 : ((q : ℤ) : ZMod N) = 1 := by
    rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by simp, ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using (dvd_neg.2 hqN)
  have c0 : ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 := h1
  have cN : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) c0
  have cl : ((σ 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) c0
  have d1 : ((σ 1 1 : ℤ) : ZMod N) = 1 := by rw [show ((σ 1 1 : ℤ) : ZMod N) = ((mat σ 1 1 : ℤ) : ZMod N) from rfl, h2]; simpa using hq1
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have a1 : ((σ 0 0 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, d1, cN, mul_one, mul_zero, sub_zero] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]; exact ⟨a1, d1, cN⟩
  · rw [Gamma0_mem]; exact cl

theorem tq_sum_tendsto (N l : ℕ) (k : ℤ) (q : ℕ) (hq : q.Prime) (hN : 0 < N) (hl : 0 < l)
    (hqM : ((N * l : ℕ) : ℤ) ∣ (q : ℤ) - 1) (σ : SL(2, ℤ)) (hσ : σ ∈ Lev N l)
    (f : ModularForm (Lev N l) k) (γ : SL(2, ℤ)) :
    Tendsto (TqF k q σ ⇑f ∣[k] γ) atImInfty
      (𝓝 (((1 : ℂ) + (q : ℂ) ^ (k - 1)) * valueAtInfty (⇑f ∣[k] γ))) := by
  have hM : 0 < N * l := Nat.mul_pos hN hl
  set c := valueAtInfty (⇑f ∣[k] γ)
  have hF := tendsto_slash_valueAtInfty N l k hN hl f γ
  let u : Fin (q + 1) → SL(2, ℤ) := fun i => if (i : ℕ) < q then ModularGroup.T ^ ((i : ℕ) : ℤ) else σ
  have hu : ∀ i, u i ∈ Lev N l := fun i => by
    by_cases h : (i : ℕ) < q
    · simp only [u, h, if_true]; exact T_zpow_mem_lev N l _
    · simp only [u, h, if_false]; exact hσ
  have hdet : ∀ i, (tqFam q σ i).det = q := fun i => by
    by_cases h : (i : ℕ) < q
    · simp [tqFam, h, Matrix.det_fin_two_of]
    · simp [tqFam, h, Matrix.det_mul, dg, Matrix.det_fin_two_of, mat]
  have hqM' : (N : ℤ) * l ∣ (q : ℤ) - 1 := by exact_mod_cast hqM
  have hcong : ∀ i a b, ((N * l : ℕ) : ℤ) ∣ tqFam q σ i a b - mat (u i) a b := fun i a b => by
    by_cases h : (i : ℕ) < q
    · simp only [tqFam, u, h, if_true, mat, ModularGroup.coe_T_zpow]
      fin_cases a <;> fin_cases b <;> simp [hqM']
    · simp only [tqFam, u, h, if_false]
      fin_cases a <;> fin_cases b <;>
        simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two, ← mul_sub_one, Dvd.dvd.mul_left hqM']
  have hdec := fun i => slash_decomp N l k q hq hM hqM f (tqFam q σ i) (u i) (hu i) (hdet i) (hcong i) γ
  choose b hb using hdec
  classical
  let P : Fin (q + 1) → Prop := fun i => (q : ℤ) ∣ (tqFam q σ i * mat γ) 0 0 ∧ (q : ℤ) ∣ (tqFam q σ i * mat γ) 1 0
  let v : Fin (q + 1) → ℂ := fun i => if P i then (q : ℂ) ^ (k - 1) * c else (q : ℂ)⁻¹ * c
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hterm : ∀ i, Tendsto ((⇑f ∣[k] toGL (tqFam q σ i)) ∣[k] γ) atImInfty (𝓝 (v i)) := fun i => by
    rw [hb i]
    by_cases h : P i
    · have := tendsto_slash_upper k _ c q (b i) 1 (by exact_mod_cast hq.pos) one_pos hF
      simp only [P] at h
      simp only [v, P, h, and_self, if_true]
      convert this using 2
      push_cast; simp
    · have := tendsto_slash_upper k _ c 1 (b i) q one_pos (by exact_mod_cast hq.pos) hF
      simp only [P] at h
      simp only [v, P, h, if_false]
      convert this using 2
      push_cast
      rw [one_mul, ← zpow_add₀ hq0, show k - 1 + -k = -1 by ring, zpow_neg_one]
  have hsum : TqF k q σ ⇑f ∣[k] γ = ∑ i, (⇑f ∣[k] toGL (tqFam q σ i)) ∣[k] γ := by
    simp [TqF, hkF, SlashAction.sum_slash]
  rw [hsum]
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin (q + 1))) (fun i _ => hterm i)
  refine (hlim.congr (fun τ => by simp)).mono_right (le_of_eq (congrArg _ ?_))
  have hcard := card_dvd_col_eq_one q σ γ hq
  have hcard2 : (Finset.univ.filter fun i : Fin (q + 1) => ¬ P i).card = q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (q + 1)))) P
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [P] at this ⊢
    omega
  simp only [v]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard, hcard2]
  simp only [nsmul_eq_mul, Nat.cast_one, one_mul]
  field_simp
  ring

theorem tq_sub_smul_cuspForm : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime →
    q % (N * l) = 1 → IsDiam N l (q : ZMod N) σ →
    ∀ f : ModularForm (Lev N l) (k : ℤ), ∃ h : CuspForm (Lev N l) (k : ℤ),
      ⇑h = TqF (k : ℤ) q σ ⇑f - ((1 : ℂ) + (q : ℂ) ^ (k - 1)) • ⇑f := by
  intro N l k hN hl hlN hk q σ hq hqmod hdiam f
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  have hM : 0 < N * l := Nat.mul_pos hN0 hl0
  have hqM : ((N * l : ℕ) : ℤ) ∣ (q : ℤ) - 1 := by
    refine ⟨((q / (N * l) : ℕ) : ℤ), ?_⟩
    have := Nat.div_add_mod q (N * l)
    rw [hqmod] at this
    have h2 : (q : ℤ) = ((N * l : ℕ) : ℤ) * ((q / (N * l) : ℕ) : ℤ) + 1 := by exact_mod_cast this.symm
    linarith
  have hqN : (N : ℤ) ∣ (q : ℤ) - 1 := Dvd.dvd.trans (by push_cast; exact dvd_mul_right _ _) hqM
  have hqNl : ¬ q ∣ N * l := by
    intro h
    have h1 := Nat.le_of_dvd hM h
    have h2 : q % (N * l) = q := Nat.mod_eq_of_lt (lt_of_le_of_ne h1 (by
      intro e; rw [e, Nat.mod_self] at hqmod; exact absurd hqmod (by norm_num)))
    rw [h2] at hqmod; exact hq.one_lt.ne' hqmod
  have hσ := diam_mem_lev N l q hqN σ hdiam
  obtain ⟨f', hf'⟩ : ∃ f' : ModularForm (Lev N l) (k : ℤ), ⇑f' = TqF (k : ℤ) q σ ⇑f := by
    obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
    rw [hT _ _ _ _ hq.pos]
    exact GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN0 hq hqNl ((hD N l q σ).1 (by simpa using hdiam)) f
  let G : ModularForm (Lev N l) (k : ℤ) := f' - ((1 : ℂ) + (q : ℂ) ^ (k - 1)) • f
  have hG : ⇑G = TqF (k : ℤ) q σ ⇑f - ((1 : ℂ) + (q : ℂ) ^ (k - 1)) • ⇑f := by
    simp [G, hf']
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI := lev_finiteIndex N l
  refine ⟨{ toSlashInvariantForm := G.toSlashInvariantForm, holo' := G.holo', zero_at_cusps' := ?_ }, hG⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  change IsZeroAtImInfty ((⇑G) ∣[(k : ℤ)] γ)
  rw [hG, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.SL_smul_slash]
  have h1 := tq_sum_tendsto N l k q hq hN0 hl0 hqM σ hσ f γ
  have h2 := (tendsto_slash_valueAtInfty N l k hN0 hl0 f γ).const_smul ((1 : ℂ) + (q : ℂ) ^ (k - 1))
  have h3 := h1.sub h2
  have hz : (q : ℂ) ^ ((k : ℤ) - 1) = (q : ℂ) ^ (k - 1) := by
    rw [← zpow_natCast]; congr 1; omega
  rw [hz, smul_eq_mul, sub_self] at h3
  exact h3.congr (fun τ => by simp [sub_eq_add_neg])

end GlobalTheory.HeckeFamilyMatrices.EisT
