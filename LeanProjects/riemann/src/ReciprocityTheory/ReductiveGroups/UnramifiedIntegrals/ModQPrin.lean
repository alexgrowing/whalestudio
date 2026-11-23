import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.analytic {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  obtain ⟨g, hg⟩ := hf
  have hfg : f = ⇑g := funext fun τ => (hg τ).symm
  subst hfg
  exact ModularFormClass.analyticAt_cuspFunction_zero g one_pos (by simp)

theorem qExp_AA_pow (n : ℕ) : qExpansion 1 (fun τ => AA τ ^ n) = aC ^ n := by
  induction n with
  | zero =>
    have : (fun τ => AA τ ^ 0) = (1 : ℍ → ℂ) := by funext τ; simp
    rw [this, qExpansion_one, pow_zero]
  | succ n ih =>
    have : (fun τ => AA τ ^ (n + 1)) = (fun τ => AA τ ^ n) * AA := by funext τ; simp [pow_succ]
    rw [this, qExpansion_mul (isMF_AA.pow n).analytic isMF_AA.analytic, ih, pow_succ, aC_eq]

theorem aC_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  have h4 : PowerSeries.coeff 0 e4Z = 1 := by rw [e4Z, PowerSeries.coeff_mk, if_pos rfl]
  rw [aC, aZ, PowerSeries.coeff_map]
  simp [pow_succ, PowerSeries.coeff_mul, h4]

theorem IsMF.div_DD {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f)
    (h0 : PowerSeries.coeff 0 (qExpansion 1 f) = 0) :
    ∃ h : ℍ → ℂ, IsMF (k - 12) h ∧ (∀ τ, f τ = DD τ * h τ) ∧
      qExpansion 1 f = dC * qExpansion 1 h := by
  obtain ⟨g, hg⟩ := hf
  obtain rfl : (⇑g : ℍ → ℂ) = f := funext hg
  refine ⟨CuspForm.discriminantEquiv (toCuspForm g h0), ⟨_, fun _ => rfl⟩, fun τ => ?_, ?_⟩
  · exact (discriminant_mul_discriminantEquiv_apply (toCuspForm g h0) τ).symm
  · rw [dC_eq]
    exact qExpansion_eq_qExpansion_discriminant_mul g h0

theorem coeff_mul_low (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by
  constructor
  · intro i hi
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hG x.2 (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hV, one_mul]
    · intro x hx hne
      obtain ⟨a, b⟩ := x
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hb : b < n := by
        by_contra hb'
        apply hne
        have ha0 : a = 0 := by simp only at hx; omega
        have hbn : b = n := by simp only at hx; omega
        rw [ha0, hbn]
      rw [hG b hb, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem exists_dC_inv : ∃ v : PowerSeries ℤ, PowerSeries.coeff 0 v = 1 ∧
    ∀ H : PowerSeries ℂ, PowerSeries.X * H = v.map (Int.castRingHom ℂ) * (dC * H) := by
  set u : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) dZ with hu
  have hd0 : PowerSeries.coeff 0 dZ = 0 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul]
  have hd1 : PowerSeries.coeff 1 dZ = 1 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num
  have hXu : dZ = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    · rw [hd0, PowerSeries.coeff_zero_X_mul]
    · rw [PowerSeries.coeff_succ_X_mul, hu, PowerSeries.coeff_mk]
  have hu0 : PowerSeries.constantCoeff u = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, PowerSeries.coeff_mk, zero_add, hd1, Units.val_one]
  refine ⟨PowerSeries.invOfUnit u 1, ?_, fun H => ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  · have hinv := PowerSeries.mul_invOfUnit u 1 hu0
    have hdC : dC = PowerSeries.X * u.map (Int.castRingHom ℂ) := by
      rw [dC, hXu, map_mul, PowerSeries.map_X]
    rw [hdC]
    have h1 : (u.map (Int.castRingHom ℂ)) * (PowerSeries.invOfUnit u 1).map (Int.castRingHom ℂ) = 1 := by
      rw [← map_mul, hinv, map_one]
    linear_combination (-(PowerSeries.X * H)) * h1

theorem coeffIn_of_dC_mul (R : Subring ℂ) (H : PowerSeries ℂ) (h : CoeffIn R (dC * H)) : CoeffIn R H := by
  obtain ⟨v, -, hv⟩ := exists_dC_inv
  intro n
  rw [← PowerSeries.coeff_succ_X_mul, hv H, PowerSeries.coeff_mul]
  refine sum_mem fun x _ => mul_mem ?_ (h x.2)
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem _ _

theorem low_of_dC_mul (H : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (dC * H) = 0) (h1 : PowerSeries.coeff n0 (dC * H) = u) :
    ∃ k, n0 = k + 1 ∧ (∀ n < k, PowerSeries.coeff n H = 0) ∧ PowerSeries.coeff k H = u := by
  obtain ⟨v, hv0, hv⟩ := exists_dC_inv
  have hV : PowerSeries.coeff 0 (v.map (Int.castRingHom ℂ)) = 1 := by
    rw [PowerSeries.coeff_map, hv0, map_one]
  obtain ⟨hlow, hn0⟩ := coeff_mul_low _ _ hV n0 h0
  rw [h1, ← hv H] at hn0
  rw [← hv H] at hlow
  rcases n0 with _ | k
  · rw [PowerSeries.coeff_zero_X_mul] at hn0
    exact absurd hn0.symm hu
  · refine ⟨k, rfl, fun n hn => ?_, ?_⟩
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hlow _ (by omega)
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hn0

theorem exists_integral_poly_of_qExpansion (R : Subring ℂ) (N : ℕ) : ∀ f : ℍ → ℂ, IsMF (12 * (N : ℤ)) f →
    CoeffIn R (qExpansion 1 f) →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      (∀ τ, f τ = DD τ ^ N * P.eval (jT τ)) ∧
      ∀ (n0 : ℕ) (u : ℂ), u ≠ 0 → (∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0) →
        PowerSeries.coeff n0 (qExpansion 1 f) = u → P.leadingCoeff = u := by
  induction N with
  | zero =>
    intro f hf hR
    obtain ⟨g, hg⟩ := hf.congr_weight (k' := 0) (by simp)
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const g
    have hfc : f = c • (1 : ℍ → ℂ) := by
      funext τ; rw [← hg τ, hc]; simp
    have hq : qExpansion 1 f = c • (1 : PowerSeries ℂ) := by
      have h1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := by
        have : IsMF 0 (1 : ℍ → ℂ) := ⟨1, fun τ => by simp⟩
        exact this.analytic
      rw [hfc, qExpansion_smul h1, qExpansion_one]
    refine ⟨Polynomial.C c, fun i => ?_, by simp, fun τ => ?_, fun n0 u hu h0 h1 => ?_⟩
    · have := hR 0
      rw [hq] at this
      rw [Polynomial.coeff_C]
      split_ifs
      · simpa using this
      · exact R.zero_mem
    · rw [hfc]; simp
    · rw [hq] at h1
      rw [Polynomial.leadingCoeff_C]
      cases n0 with
      | zero => simpa using h1
      | succ k =>
        exfalso; apply hu; rw [← h1]
        simp [PowerSeries.coeff_one]
  | succ N ih =>
    intro f hf hR
    set a0 : ℂ := PowerSeries.coeff 0 (qExpansion 1 f) with ha0
    have hA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => AA τ ^ (N + 1)) :=
      (isMF_AA.pow (N + 1)).congr_weight (by ring)
    have hcA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => a0 * AA τ ^ (N + 1)) := hA.const_mul a0
    have hg : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => f τ - a0 * AA τ ^ (N + 1)) := hf.sub hcA
    have hqg : qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1)) =
        qExpansion 1 f - a0 • aC ^ (N + 1) := by
      have e1 : (fun τ => f τ - a0 * AA τ ^ (N + 1)) = f - a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      have e2 : (fun τ => a0 * AA τ ^ (N + 1)) = a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      rw [e1, qExpansion_sub hf.analytic (e2 ▸ hcA.analytic), qExpansion_smul hA.analytic,
        qExp_AA_pow]
    have haR : a0 ∈ R := hR 0
    have hac : ∀ n, PowerSeries.coeff n (aC ^ (N + 1)) ∈ R := by
      intro n
      have : aC ^ (N + 1) = (aZ ^ (N + 1)).map (Int.castRingHom ℂ) := by rw [map_pow]; rfl
      rw [this, PowerSeries.coeff_map]
      exact intCast_mem R _
    have hac0 : PowerSeries.coeff 0 (aC ^ (N + 1)) = 1 := by
      have := aC_coeff_zero
      simp only [PowerSeries.coeff_zero_eq_constantCoeff] at this ⊢
      rw [map_pow, this, one_pow]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1))) = 0 := by
      rw [hqg, map_sub, PowerSeries.coeff_smul, hac0]; simp [ha0]
    obtain ⟨h, hh, hfh, hqh⟩ := hg.div_DD hg0
    have hh' : IsMF (12 * (N : ℤ)) h := hh.congr_weight (by push_cast; ring)
    have hRh : CoeffIn R (qExpansion 1 h) := by
      apply coeffIn_of_dC_mul
      rw [← hqh, hqg]
      intro n
      rw [map_sub, PowerSeries.coeff_smul]
      exact R.sub_mem (hR n) (R.mul_mem haR (hac n))
    obtain ⟨P', hP1, hP2, hP3, hP4⟩ := ih h hh' hRh
    refine ⟨Polynomial.C a0 * Polynomial.X ^ (N + 1) + P', fun i => ?_, ?_, fun τ => ?_,
      fun n0 u hu h0 h1 => ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
      refine R.add_mem ?_ (hP1 i)
      split_ifs
      · exact haR
      · exact R.zero_mem
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · have hD := DD_ne_zero τ
      have e := hfh τ
      rw [hP3 τ] at e
      have : f τ = a0 * AA τ ^ (N + 1) + DD τ * (DD τ ^ N * P'.eval (jT τ)) := by
        rw [← e]; ring
      rw [this]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hj : DD τ ^ (N + 1) * jT τ ^ (N + 1) = AA τ ^ (N + 1) := by
        rw [← mul_pow, jT, mul_div_cancel₀ _ hD]
      rw [← hj]; ring
    · by_cases hz : a0 = 0
      · have hq' : qExpansion 1 f = dC * qExpansion 1 h := by
          rw [← hqh, hqg, hz]; simp
        rw [hq'] at h0 h1
        obtain ⟨k, -, hk0, hk1⟩ := low_of_dC_mul _ n0 u hu h0 h1
        rw [hz]; simp only [map_zero, zero_mul, zero_add]
        exact hP4 k u hu hk0 hk1
      · have hn0 : n0 = 0 := by
          by_contra hne
          exact hz (h0 0 (Nat.pos_of_ne_zero hne))
        subst hn0
        rw [Polynomial.leadingCoeff_add_of_degree_lt', Polynomial.leadingCoeff_mul_X_pow,
          Polynomial.leadingCoeff_C]
        · exact h1
        · rw [Polynomial.degree_C_mul_X_pow _ hz]
          refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP2) ?_
          exact_mod_cast Nat.lt_succ_self N

theorem qPrin (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, h1, h2, h3, -⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, h1, h2, h3⟩

theorem qPrin_low (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0)
    (h1 : PowerSeries.coeff n0 (qExpansion 1 f) = u) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧ P.leadingCoeff = u ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, hc, hd, he, hl⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, hc, hd, hl n0 u hu h0 h1, he⟩

end ReciprocityTheory.ChartRestriction.L1
