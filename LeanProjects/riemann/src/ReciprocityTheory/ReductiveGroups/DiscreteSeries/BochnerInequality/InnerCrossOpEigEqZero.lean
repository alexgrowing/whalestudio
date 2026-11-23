import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section One

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem Wm_le_ncV : Wm ε E V ≤ ncV ε V 1 := by
  unfold Wm
  exact iSup₂_le fun _ _ => inf_le_right

theorem inner_crossOp_eig_eq_zero (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by
  have h := crossOp_symm hU 1 0 u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne : (θ : ℂ) ≠ (θ' : ℂ) := by exact_mod_cast hθ
  by_contra h0
  exact hne (mul_right_cancel₀ h0 h)

theorem Wm_perp_Wp (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by
  have h : (Wm ε E V).IsOrtho (Wp ε E V) := by
    unfold Wm Wp
    refine Submodule.isOrtho_iSup_left.mpr fun θ => Submodule.isOrtho_iSup_left.mpr fun hθ =>
      Submodule.isOrtho_iSup_right.mpr fun θ' => Submodule.isOrtho_iSup_right.mpr fun hθ' => ?_
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hu hv
    exact inner_crossOp_eig_eq_zero hU (ne_of_lt (hθ.trans hθ')) hu.1 hv.1
  exact Submodule.isOrtho_iff_inner_eq.mp h x hx y hy

theorem mem_V_of_mem_ncV {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k)
    (κ : Fin k → Fin n × Fin n) : F κ ∈ V := by
  exact ncV_mem hF κ

private theorem casimirK_eq_casValK_smul_of_isKHWVec {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X}
    (hw : IsKHWVec ε A μ w) : casimirK ε A w = (casValK ε μ : ℂ) • w := by
  have hA' : ∀ a b c d : Fin n, A a b * A c d - A c d * A a b =
      (if b = c then A a d else 0) - (if d = a then A c b else 0) := hA
  have term : ∀ a b : Fin n, ε b = ε a → A a b (A b a w) =
      ((((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0) : ℝ)) : ℂ) • w := by
    intro a b hab
    rcases lt_trichotomy b a with h | h | h
    · rw [hw.2 b a h hab, map_zero, if_neg (ne_of_lt h), if_neg (lt_asymm h)]
      simp
    · subst h
      rw [if_pos rfl, if_neg (lt_irrefl b), add_zero, hw.1 b, map_smul, hw.1 b, smul_smul,
        ← Complex.ofReal_mul, ← sq]
    · have e := LinearMap.congr_fun (hA' a b b a) w
      simp only [LinearMap.sub_apply, Module.End.mul_apply, eq_self_iff_true, if_true,
        hw.2 a b h hab.symm, map_zero, sub_zero] at e
      rw [e, if_neg (ne_of_gt h), if_pos h, hw.1 a, hw.1 b]
      simp [sub_smul]
  have hsum : casimirK ε A w = ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) : ℝ) : ℂ) • w := by
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, Complex.ofReal_sum,
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      term a b (Finset.mem_filter.mp hb).2
  have hA2 : ∀ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if b = a then μ a ^ 2 else 0) + (if a < b then μ a - μ b else 0)) =
      μ a ^ 2 + ((∑ b, if a < b ∧ ε b = ε a then μ a else 0) -
        ∑ b, if a < b ∧ ε b = ε a then μ b else 0) := by
    intro a
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    have h2 : μ a ^ 2 = ∑ b, (if b = a then μ a ^ 2 else 0) := by simp
    conv_rhs => rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  have hC : (∑ a, ∑ b, if a < b ∧ ε b = ε a then μ b else 0) =
      ∑ a, ∑ b, if b < a ∧ ε b = ε a then μ a else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : b < a ∧ ε a = ε b
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.symm⟩]
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.symm⟩]
  have hρ : ∀ a, 2 * rhoC ε a = (∑ b, if a < b ∧ ε b = ε a then (1 : ℝ) else 0) -
      ∑ b, if b < a ∧ ε b = ε a then (1 : ℝ) else 0 := by
    intro a
    simp only [rhoC]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  have hR : casValK ε μ = ∑ a, (μ a ^ 2 + μ a * (2 * rhoC ε a)) := by
    simp only [casValK, nsq, dot, Pi.add_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum, hR, Finset.sum_congr rfl fun a _ => hA2 a]
  congr 2
  simp only [hρ, mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hC]

theorem crossOp_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by
  obtain ⟨γ, hγ, hνγ⟩ := khw_big_weight hE hV hx hx0 hν
  refine ⟨(γ 0).1, (γ 0).2, hγ 0, ?_, ?_⟩
  · rw [Fin.sum_univ_one] at hνγ
    rw [← hνγ]
    abel
  · have hm : casimirK ε (mAct E 1) x = (casValK ε (lowK ε lam) : ℂ) • x := by
      ext κ
      rw [casimirK_mAct_apply, casimirK_irr hE hV _ (ncV_mem hx κ)]
      rfl
    have hcas := LinearMap.congr_fun (casimirK_bAct (ε := ε) (E := E) 1) x
    rw [casimirK_eq_casValK_smul_of_isKHWVec (bAct_isGlRep hE 1) hν] at hcas
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Fin.sum_univ_one, factorCasimir_ncV_one hx,
      hm, two_smul] at hcas
    rw [two_smul]
    push_cast
    rw [sub_smul, sub_smul, hcas]
    abel

theorem Wm_kStable (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by
  intro a b hab v hv
  have hVs : IsKStableSub ε E V := hV.2.1
  have hle : Wm ε E V ≤ (Wm ε E V).comap (bAct E 1 a b) := by
    unfold Wm
    refine iSup₂_le fun θ hθ x hx => ?_
    rw [Submodule.mem_comap]
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hx
    have hc : crossOp ε E 1 0 (bAct E 1 a b x) = bAct E 1 a b (crossOp ε E 1 0 x) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) x
    have hmem : bAct E 1 a b x ∈
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := by
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      refine ⟨?_, ncV_kStable hVs 1 a b hab x hx.2⟩
      rw [hc, hx.1, map_smul]
    exact Submodule.mem_iSup_of_mem θ (Submodule.mem_iSup_of_mem hθ hmem)
  exact hle hv

end One

end ReciprocityTheory.ChartRestriction.DS
