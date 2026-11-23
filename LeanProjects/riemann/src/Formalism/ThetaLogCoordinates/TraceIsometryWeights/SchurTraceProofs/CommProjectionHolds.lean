import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem isoC_stable (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    GlStableC p LL j Cs (IsoC p LL j Cs la) := by
  intro c hc d hd x hx
  rw [IsoC, Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c hc d hd x (hx S hS)

theorem hwc_le_isoC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    HWC p LL j Cs la ≤ IsoC p LL j Cs la := by
  rw [IsoC]
  exact le_sInf fun S hS => hS.1

theorem coeff_glAct_diag (LL : Letters N) (j : ℕ) (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) :
    coeff m (glAct p LL j c c x) = ((wt LL j c m : ℤ) : ℚ_[p]) * coeff m x := by
  classical
  conv_lhs => rw [x.as_sum]
  rw [map_sum, coeff_sum]
  simp only [glAct_diag_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro hm
    rw [if_pos rfl, notMem_support_iff.mp hm, mul_zero]

theorem wtSpC_iff_eig (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ ∀ c ∈ Cs, glAct p LL j c c x = ((la c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h c hc
    ext m
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul]
    by_cases hm : coeff m x = 0
    · rw [hm, mul_zero, mul_zero]
    · have := h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c hc
      rw [this]
  · intro h m hm c hc
    have hm' : coeff m x ≠ 0 := mem_support_iff.mp (Finset.mem_coe.mp hm)
    have e := congrArg (coeff m) (h c hc)
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul] at e
    have := mul_right_cancel₀ hm' e
    exact_mod_cast this

theorem hwc_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ HWC p LL j Cs la, A x ∈ HWC p LL j Cs la := by
  intro x hx
  rw [HWC, Submodule.mem_inf] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [wtSpC_iff_eig]
    intro c hc
    rw [← hA c hc c hc, (wtSpC_iff_eig LL j Cs la x).mp hx.1 c hc, map_smul]
  · have h2 := hx.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, h2 c d hcd, map_zero]

theorem isoC_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la := by
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap A := by
    conv_lhs => rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      exact hwc_le_isoC LL j Cs la (hwc_map_of_comm LL j Cs A hA la x hx)
    · intro c hc d hd x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hA c hc d hd]
      exact isoC_stable LL j Cs la c hc d hd _ hx
  exact fun x hx => hle hx

theorem iSup_isoC_map (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Q : (Fin r → ℤ) → Prop)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) :
    ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la),
      A x ∈ (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) := by
  have hle : (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) ≤
      (⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la).comap A := by
    refine iSup_le fun la => iSup_le fun hla => ?_
    intro x hx
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le la (le_iSup_of_le hla le_rfl) :
      IsoC p LL j Cs la ≤ ⨆ (la : Fin r → ℤ) (_ : Q la), IsoC p LL j Cs la) (hA la x hx)
  exact fun x hx => hle hx

theorem typeProj_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ la, ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la) : P ∘ₗ A = A ∘ₗ P := by
  obtain ⟨hPP, hr, hk⟩ := hP
  have hPP' : ∀ x, P (P x) = P x := fun x => congrArg (fun f => f x) hPP
  have hR : ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P := by
    rw [hr]; exact iSup_isoC_map LL j Cs (fun la => la ∈ T) A hA
  have hK : ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P := by
    rw [hk]; exact iSup_isoC_map LL j Cs (fun la => la ∉ T) A hA
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : P (A (P x)) = A (P x) := by
    obtain ⟨y, hy⟩ := hR (P x) ⟨x, rfl⟩
    rw [← hy, hPP']
  have h2 : P (A (x - P x)) = 0 := by
    apply hK
    rw [LinearMap.mem_ker, map_sub, hPP', sub_self]
  rw [map_sub, map_sub, h1, sub_eq_zero] at h2
  exact h2

theorem comm_projection_holds : CommP := by
  intro p _ N r LL j j' Cs Cs' T T' P P' hj hC hP hP'
  have h1 : ∀ c ∈ Cs', ∀ d ∈ Cs', ∀ x, P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
    intro c hc d hd x
    have := typeProj_comm LL j Cs T P hP (glAct p LL j' c d) (by
      intro la y hy
      rw [glAct_split LL hj c d, LinearMap.add_apply]
      refine Submodule.add_mem _ (isoC_stable LL j Cs la c (hC hc) d (hC hd) y hy) ?_
      exact isoC_map_of_comm LL j Cs (midAct p LL j j' c d)
        (fun c' _ d' _ z => midAct_comm LL j j' c d c' d' z) la y hy)
    exact congrArg (fun f => f x) this
  exact (typeProj_comm LL j' Cs' T' P' hP' P (isoC_map_of_comm LL j' Cs' P h1)).symm

end Formalism.InvariantFactorPaths.PW
