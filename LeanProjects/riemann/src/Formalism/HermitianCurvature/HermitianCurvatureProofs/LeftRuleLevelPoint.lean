import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HpkMulSingleEsI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeKeepsCharacter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section hpart

variable {k r j : ℕ}

theorem hpk_row_eI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (eI k r c) l = if l = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_eI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (eI k r c) x * Hpk k r = Matrix.single p (esI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
  · rw [hpk_row_eI]
    by_cases hi : i = p <;> by_cases hl : l = esI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hpart1_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  rfl

theorem hpart2_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  rfl

theorem nN_smul_real (hj : j + 1 ≤ r) (a : Fin j → ℂ) (t : ℝ) :
    nN k r j hj (fun c => (t : ℂ) * a c) = (t : ℂ) • nN k r j hj a := by
  unfold nN
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_sub, smul_smul, smul_smul, map_mul, Complex.conj_ofReal]

theorem ell_nL (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a : Fin j → ℂ) :
    ell k r z (nL k r j hj a) = -conj (a ⟨j - 1, by omega⟩) := by
  unfold ell
  rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin r)]
  · rw [dif_pos (show j - 1 + 1 < r by omega), SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]),
      zero_add, Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin j)]
    · have e2 : eI k r ⟨j - 1 + 1, by omega⟩ = eI k r ⟨j, by omega⟩ := by ext; simp [eI]; omega
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, e2]
      rw [show (eI k r ⟨((⟨j - 1, by omega⟩ : Fin j) : ℕ), by omega⟩ : Fin (2 * r + k + 1)) = eI k r ⟨j - 1, by omega⟩
        from rfl, Matrix.single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub,
        Matrix.single_apply_of_row_ne, mul_zero, neg_zero]
      intro h
      apply hb
      have := congrArg Fin.val h
      simp only [eI] at this
      exact Fin.ext this
    · simp
  · intro a' _ ha'
    have hne : a'.val ≠ j - 1 := fun h => ha' (Fin.ext h)
    split_ifs with h
    · rw [SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]), zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
      rw [if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      omega
    · have hrow : ∀ q, nL k r j hj a (eI k r a') q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a') q := by
        intro q
        rw [SingleEntryHermitianProducts.nL_apply, Finset.sum_eq_zero, add_zero]
        intro b _
        rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
        rw [if_neg, mul_zero, neg_zero]
        rintro ⟨h1, _⟩
        have e1 := congrArg Fin.val h1
        simp only [eI] at e1
        have := b.isLt
        omega
      rw [Matrix.mulVec, dotProduct]
      simp_rw [hrow]
      rw [← dotProduct, ← Matrix.mulVec, Matrix.one_mulVec, hz _ (Or.inl (by simp [eI]))]
  · simp

end hpart

section deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r j : ℕ}

theorem hpk_row_esI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (esI k r c) l = if l = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_esI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (esI k r c) x * Hpk k r = Matrix.single p (eI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r c)]
  · rw [hpk_row_esI]
    by_cases hi : i = p <;> by_cases hl : l = eI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hM_lie (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) :
    (hM k r j hj x y s)ᴴ * Hpk k r + Hpk k r * hM k r j hj x y s = 0 := by
  unfold hM
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
    SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, single_mul_hpk_eI,
    single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI]
  abel

theorem psi_nL_hasDeriv (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : Fin j → ℂ) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)))
      (a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩)) 0 := by
  set R : ℝ := (cStd * -conj (a ⟨j - 1, by omega⟩)).re with hR
  have hfun : (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c))) =
      fun t : ℝ => Complex.exp (Complex.I * (((t * R : ℝ)) : ℂ)) := by
    funext t
    unfold psi
    rw [ell_nL hj hj1 z hz]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, hR]
    rw [show cStd * -((t : ℂ) * conj (a ⟨j - 1, by omega⟩)) = (t : ℂ) * (cStd * -conj (a ⟨j - 1, by omega⟩)) by ring,
      Complex.re_ofReal_mul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => ((t * R : ℝ) : ℂ)) ((R : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const R).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).cexp
  have hval : Complex.I * ((R : ℝ) : ℂ) = a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩) := by
    apply Complex.ext <;> simp [hR, cStd, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  rw [← hval]
  simpa using h2

theorem rdV_hM (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (hj1 : 1 ≤ j) (hz : inWb k r z) (hS : Q.SmoothLev k r 0 Dm Ψ) (hZ : Z.det ≠ 0)
    (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) (hx : x0 k r j hj Z τ γ ∈ Dm)
    (hEq : ∀ a : Fin j → ℂ,
      Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ))
    (b : Fin j) (s : ℂ) :
    RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ (x0 k r j hj Z τ γ) =
      (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩ - conj (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩)) • Ψ (x0 k r j hj Z τ γ) := by
  set x₁ := x0 k r j hj Z τ γ with hx₁
  have hxG : x₁ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS x₁ ⟨hxG, hx⟩
  have hd : DifferentiableAt ℝ F x₁ := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  set a : Fin j → ℂ := fun c => s * τ * Z⁻¹ b c with ha
  have hrd : RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ x₁ =
      fderiv ℝ F x₁ (x₁ * hM k r j hj (Fin.last j) b.castSucc s) :=
    (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hxU hxG ⟨hM_lie hj _ _ s, fun a ha => absurd ha (Nat.not_lt_zero _)⟩ hd
      hFU).deriv
  rw [hrd, hx₁, level_point_conj_unipotent hj hZ hτ γ b s, ← hx₁]
  have hc : HasDerivAt (fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) (nN k r j hj a * x₁) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (h0.smul_const (nN k r j hj a * x₁)).const_add x₁
    rw [one_smul] at this
    exact this
  have hcF := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hcurve : ∀ t : ℝ, x₁ + (t : ℂ) • (nN k r j hj a * x₁) = nL k r j hj (fun c => (t : ℂ) * a c) * x₁ := by
    intro t
    rw [nL_eq, nN_smul_real, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hev : (F ∘ fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) =ᶠ[𝓝 0]
      fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)) • Ψ x₁ := by
    have hUn : U ∈ 𝓝 (x₁ + ((0 : ℝ) : ℂ) • (nN k r j hj a * x₁)) := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hU.mem_nhds hxU
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ U :=
      hc.continuousAt.preimage_mem_nhds hUn
    filter_upwards [hmem] with t ht
    have hG : x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ Q.Glev k r 0 := by
      rw [hcurve t]; exact Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj _) hxG
    simp only [Function.comp]
    rw [← hFU _ ht hG, hcurve t, hEq]
  have h2 := (psi_nL_hasDeriv hj hj1 z hz a).smul_const (Ψ x₁)
  exact (hcF.congr_of_eventuallyEq hev.symm).unique h2

theorem left_rule_level_point : CutHL.LeftActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single hj b, hpart2_single hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end deriv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
