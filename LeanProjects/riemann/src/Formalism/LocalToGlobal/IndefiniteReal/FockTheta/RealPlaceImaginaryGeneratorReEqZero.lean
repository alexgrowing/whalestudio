import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.CCR

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realPlace_imaginaryGenerator_re_eq_zero (D : D7) (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  simp [Formalism.BasicNotions.Host.xi0, map_div₀, map_neg, map_one, map_mul, map_natCast, Formalism.L2.Theta.tauE_sqrtMinusD,
    Complex.div_re]

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.what₂.Tau) : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im := by
  have h0 := realPlace_imaginaryGenerator_re_eq_zero D τ
  have hpos := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hz : tauE D τ D.host.xi0 = ((tauE D τ D.host.xi0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h0]
  nth_rewrite 1 [hz]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

theorem fockScale_sq (D : D7) (τ : D.what₂.Tau) :
    fockScale D τ ^ 2 = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
  unfold fockScale
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_embedding_hostFormConstant_eq]
  ring

theorem fockScale_pos (D : D7) (τ : D.what₂.Tau) : 0 < fockScale D τ := by
  unfold fockScale
  have h := Formalism.L2.Theta.xi_zero_im_pos D τ
  rw [norm_embedding_hostFormConstant_eq]
  exact mul_pos two_pos (Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h))

theorem heisO_add_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + c • g) = heisO ψ S T u f + c • heisO ψ S T u g := by

  funext w
  simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 where
  quasi := by intro γ w; simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩
  cont := continuous_const
  smooth := fun _ _ _ _ _ => contDiff_const

theorem theta_add_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (c : ℂ) : IsThetaFunO ψ S T (f + c • g) where
  quasi := by
    intro γ w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.quasi, hg.quasi]
    ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, by rw [AddSubgroup.coe_inf]; exact hU.inter hV, fun u hu hinf => ?_⟩
    rw [heisO_add_smul, hUf u hu.1 hinf, hVg u hu.2 hinf]
  cont := hf.cont.add (hg.cont.const_smul c)
  smooth := by
    intro k L hL hfin w
    simpa [Pi.add_apply, Pi.smul_apply] using
      (hf.smooth k L hL hfin w).add ((hg.smooth k L hL hfin w).const_smul c)

theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (c : ℂ) :
    IsThetaFunO ψ S T (c • g) := by
  have h := theta_add_smul (theta_zero ψ S T) hg c
  simpa using h

theorem theta_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := by
  have h := theta_add_smul hf hg 1
  simpa using h

theorem theta_function_linear_combination {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (a b : ℂ) : IsThetaFunO ψ S T (a • f + b • g) := theta_add (theta_smul hf a) (theta_smul hg b)

theorem aPlusAll_eq {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k : FVar D m n)
    (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k f =
      ((fockScale D k.1 : ℂ)⁻¹) • dRho hs θ k.1 (unitMap (B k.1) (B' k.1) k.2.1 k.2.2) f +
        (-((fockScale D k.1 : ℂ)⁻¹) * Complex.I) • dRho hs θ k.1 (J k.1 (unitMap (B k.1) (B' k.1) k.2.1 k.2.2)) f := by

  unfold aPlusAll aPlus crea
  first
  | module
  | rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul, neg_mul]

theorem aMinusAll_eq {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k : FVar D m n)
    (f : Mx D m n → ℂ) :
    aMinusAll hs θ J B B' k f =
      (-((fockScale D k.1 : ℂ)⁻¹)) • dRho hs θ k.1 (unitMap (B k.1) (B' k.1) k.2.1 k.2.2) f +
        (-((fockScale D k.1 : ℂ)⁻¹) * Complex.I) • dRho hs θ k.1 (J k.1 (unitMap (B k.1) (B' k.1) k.2.1 k.2.2)) f := by

  unfold aMinusAll annih
  first
  | module
  | rw [smul_add, smul_smul]

section Assembly

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem derived_action_linear_combination (hL : DRhoLin D) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (hLine : LineAtExists D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (a b : ℂ) :
    dRho (heisO ψ S T) θ τ z (a • f + b • g) =
      a • dRho (heisO ψ S T) θ τ z f + b • dRho (heisO ψ S T) θ τ z g := by
  obtain ⟨-, -, h3⟩ := hL ψ θ hstd hinf hLine S T τ
  have h0 : dRho (heisO ψ S T) θ τ z 0 = 0 := by
    have h := h3 z 1 0 0 (theta_zero ψ S T) (theta_zero ψ S T)
    simp only [one_smul, add_zero] at h
    nth_rewrite 1 [← add_zero (dRho (heisO ψ S T) θ τ z 0)] at h
    exact (add_left_cancel h).symm
  rw [h3 z b (a • f) g (theta_smul hf a) hg]
  have e : a • f = 0 + a • f := (zero_add _).symm
  rw [e, h3 z a 0 f (theta_zero ψ S T) hf, h0, zero_add]

end Assembly

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

open Classical in

theorem comm_at (hC : DRhoComm D) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (hLine : LineAtExists D)
    (τ τ' : D.what₂.Tau) (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (x : WO S T) :
    dRho (heisO ψ S T) θ τ z (dRho (heisO ψ S T) θ τ' w f) x - dRho (heisO ψ S T) θ τ' w (dRho (heisO ψ S T) θ τ z f) x =
      if τ = τ' then (-(2 * Real.pi : ℂ) * Complex.I *
        (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) z w : ℂ)) * f x else 0 := by
  have h := congrFun (hC ψ θ hstd hinf hLine S T τ τ' z w f hf) x
  rw [Pi.sub_apply] at h
  rw [h]
  split_ifs <;> simp

open Classical in
theorem ccrTheta_of (hUB : UnitBracket) (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : CCRTheta D := by
  intro hLine ψ θ S T sS sT BS BT pS pT hP
  have hstd := hP.std
  have hinf := hP.inf
  have hTh : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g : WO S T → ℂ},
      IsThetaFunO ψ S T g → IsThetaFunO ψ S T (dRho (heisO ψ S T) θ τ z g) :=
    fun τ z g hg => (hT ψ θ hstd hinf hLine S T τ z g hg).1
  have keyEq : ∀ (τ : D.what₂.Tau) (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g : WO S T → ℂ},
      IsThetaFunO ψ S T g → ∀ x, dRho (heisO ψ S T) θ τ z (dRho (heisO ψ S T) θ τ w g) x =
        dRho (heisO ψ S T) θ τ w (dRho (heisO ψ S T) θ τ z g) x +
          (-(2 * Real.pi : ℂ) * Complex.I * (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) z w : ℂ)) * g x := by
    intro τ z w g hg x
    have h := comm_at hC hstd hinf hLine τ τ z w hg x
    rw [if_pos rfl] at h
    linear_combination h
  have keyNe : ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g : WO S T → ℂ}, τ ≠ τ' →
      IsThetaFunO ψ S T g → ∀ x, dRho (heisO ψ S T) θ τ z (dRho (heisO ψ S T) θ τ' w g) x =
        dRho (heisO ψ S T) θ τ' w (dRho (heisO ψ S T) θ τ z g) x := by
    intro τ τ' z w g hne hg x
    have h := comm_at hC hstd hinf hLine τ τ' z w hg x
    rw [if_neg hne] at h
    linear_combination h
  have hα2 : ∀ τ : D.what₂.Tau, (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ *
      (8 * (Real.pi : ℂ) * ((tauE D τ D.host.xi0).im : ℂ)) = 1 := by
    intro τ
    have hs0 : (fockScale D τ : ℂ) ≠ 0 := by exact_mod_cast (fockScale_pos D τ).ne'
    have hs : (8 * (Real.pi : ℂ) * ((tauE D τ D.host.xi0).im : ℂ)) = (fockScale D τ : ℂ) ^ 2 := by
      have := fockScale_sq D τ
      exact_mod_cast this.symm
    rw [hs]
    field_simp
  have hUBτ := fun τ : D.what₂.Tau => hUB T.rank S.rank (pS τ) (pT τ) (gramAt D S τ) (sS τ) (BS τ)
    (gramAt D T τ) (sT τ) (BT τ) (tauE D τ D.host.xi0) (hP.onbS τ) (hP.onbT τ) (realPlace_imaginaryGenerator_re_eq_zero D τ)
    (Formalism.L2.Theta.xi_zero_im_pos D τ)
  refine ⟨theta_zero ψ S T, fun f g hf hg => theta_add hf hg, fun c f hf => theta_smul hf c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨τ, i, c⟩ f hf
    show IsThetaFunO ψ S T _
    rw [aPlusAll_eq]
    exact theta_function_linear_combination (hTh _ _ hf) (hTh _ _ hf) _ _
  · rintro ⟨τ, i, c⟩ f hf
    show IsThetaFunO ψ S T _
    rw [aMinusAll_eq]
    exact theta_function_linear_combination (hTh _ _ hf) (hTh _ _ hf) _ _
  · rintro ⟨τ, i, c⟩ e f g hf hg
    obtain ⟨-, -, h3⟩ := hL ψ θ hstd hinf hLine S T τ
    simp only [aPlusAll_eq]
    rw [h3 _ e f g hf hg, h3 _ e f g hf hg]
    module
  · rintro ⟨τ, i, c⟩ e f g hf hg
    obtain ⟨-, -, h3⟩ := hL ψ θ hstd hinf hLine S T τ
    simp only [aMinusAll_eq]
    rw [h3 _ e f g hf hg, h3 _ e f g hf hg]
    module
  · rintro ⟨τ, i, c⟩ ⟨τ', i', c'⟩ f hf
    simp only [aPlusAll_eq]
    rw [derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf), derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf),
      derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf), derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf)]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hτ : τ = τ'
    · subst hτ
      have hb := (hUBτ τ).2.2 (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ) (BT τ) i' c')
      unfold brkPP at hb
      have k1 := keyEq τ (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ) (BT τ) i' c') hf x
      have k2 := keyEq τ (unitMap (BS τ) (BT τ) i c) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
      have k3 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (unitMap (BS τ) (BT τ) i' c') hf x
      have k4 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
      linear_combination (((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹)) * k1 + (((fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k2 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * ((fockScale D τ : ℂ)⁻¹)) * k3 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k4 +
        (((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹) * (-(2 * (Real.pi : ℂ)) * Complex.I) * f x) * hb + (((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹) * (-(2 * (Real.pi : ℂ)) * Complex.I) * f x * (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) : ℂ)) * Complex.I_mul_I
    ·
      have k1 := keyNe τ τ' (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ') (BT τ') i' c') hτ hf x
      have k2 := keyNe τ τ' (unitMap (BS τ) (BT τ) i c) (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i' c')) hτ hf x
      have k3 := keyNe τ τ' (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (unitMap (BS τ') (BT τ') i' c') hτ hf x
      have k4 := keyNe τ τ' (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i' c')) hτ hf x
      linear_combination (((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ' : ℂ)⁻¹)) * k1 + (((fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ' : ℂ)⁻¹) * Complex.I)) * k2 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * ((fockScale D τ' : ℂ)⁻¹)) * k3 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * (-((fockScale D τ' : ℂ)⁻¹) * Complex.I)) * k4
  · rintro ⟨τ, i, c⟩ ⟨τ', i', c'⟩ f hf
    simp only [aPlusAll_eq, aMinusAll_eq]
    rw [derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf), derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf),
      derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf), derived_action_linear_combination hL hstd hinf hLine _ _ (hTh _ _ hf) (hTh _ _ hf)]
    by_cases hτ : τ = τ'
    · subst hτ
      by_cases hic : i = i' ∧ c = c'
      · rw [if_pos (by rw [hic.1, hic.2])]
        funext x
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hb := (hUBτ τ).2.1 i c i' c'
        rw [if_pos hic] at hb
        unfold brk at hb
        have k1 := keyEq τ (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ) (BT τ) i' c') hf x
        have k2 := keyEq τ (unitMap (BS τ) (BT τ) i c) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
        have k3 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (unitMap (BS τ) (BT τ) i' c') hf x
        have k4 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
        linear_combination (-((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹)) * k1 + (-((fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k2 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * ((fockScale D τ : ℂ)⁻¹)) * k3 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k4 +
          (-(-(2 * (Real.pi : ℂ)) * Complex.I) * f x * ((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹)) * hb +
          ((-(2 * (Real.pi : ℂ)) * Complex.I) * f x * ((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹) * (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) : ℂ) - 8 * (Real.pi : ℂ) * ((tauE D τ D.host.xi0).im : ℂ) * ((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹) * f x) * Complex.I_mul_I +
          f x * hα2 τ
      · rw [if_neg (fun h => hic (by simp only [Prod.mk.injEq] at h; exact ⟨h.2.1, h.2.2⟩))]
        funext x
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have hb := (hUBτ τ).2.1 i c i' c'
        rw [if_neg hic] at hb
        unfold brk at hb
        have k1 := keyEq τ (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ) (BT τ) i' c') hf x
        have k2 := keyEq τ (unitMap (BS τ) (BT τ) i c) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
        have k3 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (unitMap (BS τ) (BT τ) i' c') hf x
        have k4 := keyEq τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) hf x
        linear_combination (-((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹)) * k1 + (-((fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k2 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * ((fockScale D τ : ℂ)⁻¹)) * k3 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * (-((fockScale D τ : ℂ)⁻¹) * Complex.I)) * k4 +
          (-(-(2 * (Real.pi : ℂ)) * Complex.I) * f x * ((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹)) * hb + ((-(2 * (Real.pi : ℂ)) * Complex.I) * f x * ((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ : ℂ)⁻¹) * (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i' c')) : ℂ)) * Complex.I_mul_I
    · rw [if_neg (fun h => hτ (congrArg Prod.fst h))]
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have k1 := keyNe τ τ' (unitMap (BS τ) (BT τ) i c) (unitMap (BS τ') (BT τ') i' c') hτ hf x
      have k2 := keyNe τ τ' (unitMap (BS τ) (BT τ) i c) (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i' c')) hτ hf x
      have k3 := keyNe τ τ' (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (unitMap (BS τ') (BT τ') i' c') hτ hf x
      have k4 := keyNe τ τ' (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) i c)) (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i' c')) hτ hf x
      linear_combination (-((fockScale D τ : ℂ)⁻¹) * ((fockScale D τ' : ℂ)⁻¹)) * k1 + (-((fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ' : ℂ)⁻¹) * Complex.I)) * k2 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * ((fockScale D τ' : ℂ)⁻¹)) * k3 + ((-((fockScale D τ : ℂ)⁻¹) * Complex.I) * (-((fockScale D τ' : ℂ)⁻¹) * Complex.I)) * k4

end Main

end Formalism.IndefR.Fock.CCR

end
