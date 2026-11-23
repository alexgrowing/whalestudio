import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivarianceStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalarStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDualStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibilityStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem isStd_ne_one (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))
  rw [h1, AddChar.one_apply, Algebra.trace_algebraMap] at e
  have e2 : (Module.finrank ℚ F • (1 / (2 * (Module.finrank ℚ F : ℚ))) : ℚ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [e2] at e
  have e3 : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [e3, Complex.exp_pi_mul_I] at e
  norm_num at e

variable (F) in

def ratPt (y z : κ → F) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

section One

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

structure Tw (ψ : AddChar (AF F) ℂ) (d d₁ : Darboux B κ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  maps : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, e (d.rho ψ w Φ) = d₁.rho ψ w (e Φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ
  ne : ∃ Φ ∈ schA F κ, e Φ ≠ 0

def RatRel (d d₁ : Darboux B κ) : Prop := ∀ y z : κ → F, ∃ w y' z', d.e w = ratPt F y z ∧ d₁.e w = ratPt F y' z'

variable {d d₁ d₂ : Darboux B κ} {e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem rho_mem (hψ : IsStd ψ) (d : Darboux B κ) (w : W) {Φ} (hΦ : Φ ∈ schA F κ) : d.rho ψ w Φ ∈ schA F κ :=
  (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1 _ Φ hΦ

theorem eq_zero_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ} (hΦ : Φ ∈ schA F κ) (h : ∀ w, thetaSum F (d.rho ψ w Φ) = 0) :
    Φ = 0 :=
  GlobalTheory.T.theta_heisenberg_translates_separate F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 Φ hΦ fun w => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h w'

theorem rho_smul (d : Darboux B κ) (w : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : d.rho ψ w (c • Φ) = c • d.rho ψ w Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_sub (d : Darboux B κ) (w : W) (Φ Ψ : (κ → AF F) → ℂ) : d.rho ψ w (Φ - Ψ) = d.rho ψ w Φ - d.rho ψ w Ψ := by
  funext x
  simp only [Darboux.rho, schr, Pi.sub_apply]
  ring

theorem eq_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ Ψ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ)
    (h : ∀ w, thetaSum F (d.rho ψ w Φ) = thetaSum F (d.rho ψ w Ψ)) : Φ = Ψ := by
  obtain ⟨-, ⟨l, -, hl⟩, -⟩ := GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  refine sub_eq_zero.1 (eq_zero_of_theta hψ d (sub_mem hΦ hΨ) fun w => ?_)
  rw [← hl _ (rho_mem hψ d w (sub_mem hΦ hΨ)), rho_sub, map_sub, hl _ (rho_mem hψ d w hΦ), hl _ (rho_mem hψ d w hΨ), h, sub_self]

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem Tw.theta (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := by
  obtain ⟨-, ⟨l, hl0, hl⟩, -⟩ := GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  have hinv := (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).2
  obtain ⟨a, ha⟩ := GlobalTheory.T.admissible_functional_rational_invariance F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 (l ∘ₗ e) (h.adm l hl0) fun w Φ hΦ => by
    obtain ⟨u, y', z', h1, h2⟩ := hr w.1 w.2
    have e1 := h.Heisenberg₂ u Φ hΦ
    rw [Darboux.rho, Darboux.rho, h1, h2] at e1
    have e2 := rho_mem hψ d₁ u (h.maps Φ hΦ)
    rw [Darboux.rho, h2] at e2
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine (congrArg l e1).trans ?_
    rw [hl _ e2, hl _ (h.maps Φ hΦ)]
    exact hinv (y', z') _
  have ha' : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = a * thetaSum F Φ := fun Φ hΦ => by
    rw [← ha Φ hΦ, LinearMap.comp_apply, hl _ (h.maps Φ hΦ)]
  refine ⟨a, fun a0 => ?_, ha'⟩
  obtain ⟨Φ, hΦ, hne⟩ := h.ne
  refine hne (eq_zero_of_theta hψ d₁ (h.maps Φ hΦ) fun w => ?_)
  rw [← h.Heisenberg₂ w Φ hΦ, ha' _ (rho_mem hψ d w hΦ), a0, zero_mul]

theorem Tw.inj (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) {Φ} (hΦ : Φ ∈ schA F κ) (h0 : e Φ = 0) : Φ = 0 := by
  obtain ⟨c, hc, H⟩ := h.theta hψ hr
  refine eq_zero_of_theta hψ d hΦ fun w => ?_
  have := H _ (rho_mem hψ d w hΦ)
  rw [h.Heisenberg₂ w Φ hΦ, h0, ← zero_smul ℂ (0 : (κ → AF F) → ℂ), rho_smul, thetaSum_smul, zero_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hc

theorem schur (hψ : IsStd ψ) (d : Darboux B κ) (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d.rho ψ w (T Φ)) : ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ :=
  GlobalTheory.T.heisenberg_commuting_operator_scalar F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 T h1 h2 fun w Φ hΦ => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h3 w' Φ hΦ

theorem Tw.smul (h : Tw ψ d d₁ e) {c : ℂ} (hc : c ≠ 0) : Tw ψ d d₁ (c • e) where
  maps Φ hΦ := Submodule.smul_mem _ c (h.maps Φ hΦ)
  Heisenberg₂ w Φ hΦ := by rw [LinearMap.smul_apply, LinearMap.smul_apply, h.Heisenberg₂ w Φ hΦ, rho_smul]
  adm l hl g hg := by
    obtain ⟨T, hT⟩ := h.adm l hl g hg
    refine ⟨c • T, fun f => ?_⟩
    rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
  ne := by
    obtain ⟨Φ, hΦ, h0⟩ := h.ne
    exact ⟨Φ, hΦ, smul_ne_zero hc h0⟩

theorem Tw.exists_inv (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (h' : Tw ψ d₁ d e') (hr : RatRel d d₁) (hr' : RatRel d₁ d) :
    ∃ e'', Tw ψ d₁ d e'' ∧ (∀ Φ ∈ schA F κ, e'' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e'' Φ) = Φ := by
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h.ne
    exact hne (h'.inj hψ hr' (h.maps Φ hΦ) ((ha Φ hΦ).trans (by rw [a0, zero_smul])))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have h'' := h'.smul (inv_ne_zero a0)
  refine ⟨_, h'', h1, fun Φ hΦ => sub_eq_zero.1 (h''.inj hψ hr' (sub_mem (h.maps _ (h''.maps Φ hΦ)) hΦ) ?_)⟩
  rw [map_sub, h1 _ (h''.maps Φ hΦ), sub_self]

def negD (d : Darboux B κ) : Darboux (fun w w' => -B w w') κ where
  e := d.e.trans ((LinearEquiv.refl _ _).prodCongr (LinearEquiv.neg _))
  form w w' := by
    rw [d.form]
    simp
    ring

theorem negD_e (d : Darboux B κ) (w : W) : (negD d).e w = ((d.e w).1, -(d.e w).2) := rfl

theorem RatRel.neg (hr : RatRel d d₁) : RatRel (negD d) (negD d₁) := fun y z => by
  obtain ⟨w, y', z', h1, h2⟩ := hr y (-z)
  refine ⟨w, y', -z', ?_, ?_⟩
  · rw [negD_e, h1]; simp [ratPt, funext_iff]
  · rw [negD_e, h2]; simp [ratPt, funext_iff]

end One

def TwEx : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F) (d d₁ : Darboux B κ), ∃ e, Tw ψ d d₁ e

theorem schr_box {κ' : Type} [Fintype κ'] (a b : κ → AF F) (a' b' : κ' → AF F) (φ : (κ → AF F) → ℂ) (φ' : (κ' → AF F) → ℂ) :
    schr ψ (Sum.elim a a', Sum.elim b b') (boxFun φ φ') = boxFun (schr ψ (a, b) φ) (schr ψ (a', b') φ') := by
  funext x
  have e1 : (x + Sum.elim a a') ∘ Sum.inl = x ∘ Sum.inl + a := rfl
  have e2 : (x + Sum.elim a a') ∘ Sum.inr = x ∘ Sum.inr + a' := rfl
  have e3 : x ⬝ᵥ Sum.elim b b' + ⅟(2 : AF F) * (Sum.elim a a' ⬝ᵥ Sum.elim b b') =
      (x ∘ Sum.inl ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b)) + (x ∘ Sum.inr ⬝ᵥ b' + ⅟(2 : AF F) * (a' ⬝ᵥ b')) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul]
  ring

section Dbl

variable {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
  {dd dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}

theorem RatRel.dbl (hr : RatRel d d₁) (h : IsDblCoord c ξ JA JB d dd) (h₁ : IsDblCoord c ξ JA JB d₁ dd₁) : RatRel dd dd₁ := by
  intro y z
  obtain ⟨w, y', z', h1, h2⟩ := hr (y ∘ Sum.inl) (z ∘ Sum.inl)
  obtain ⟨u, y'', z'', h3, h4⟩ := hr (y ∘ Sum.inr) (-z ∘ Sum.inr)
  refine ⟨Matrix.fromCols w u, Sum.elim y' y'', Sum.elim z' (-z''), ?_, ?_⟩
  · rw [h, h1, h3]
    ext (i | i) <;> simp [ratPt]
  · rw [h₁, h2, h4]
    ext (i | i) <;> simp [ratPt]

theorem rho_box (h : IsDblCoord c ξ JA JB d dd) (w u : Matrix α β E) (φ φ' : (κ → AF F) → ℂ) :
    dd.rho ψ (Matrix.fromCols w u) (boxFun φ φ') = boxFun (d.rho ψ w φ) ((negD d).rho ψ u φ') := by
  rw [Darboux.rho, h, schr_box]
  rfl

theorem box_compat (hT : TwEx) (hψ : IsStd ψ) (hr : RatRel d d₁) (h : IsDblCoord c ξ JA JB d dd)
    (h₁ : IsDblCoord c ξ JA JB d₁ dd₁) {e ed} (he : Tw ψ d d₁ e) (hd : Tw ψ dd dd₁ ed) :
    ∃ e₂, Tw ψ (negD d) (negD d₁) e₂ ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ed (boxFun φ φ') = boxFun (e φ) (e₂ φ') := by
  obtain ⟨e₀, h₀⟩ := hT F ψ hψ κ _ _ (negD d) (negD d₁)
  obtain ⟨a, ha, Ha⟩ := he.theta hψ hr
  obtain ⟨b, hb, Hb⟩ := h₀.theta hψ hr.neg
  obtain ⟨t, ht, Ht⟩ := hd.theta hψ (hr.dbl h h₁)
  have h₂ := h₀.smul (div_ne_zero ht (mul_ne_zero ha hb))
  refine ⟨_, h₂, fun φ hφ φ' hφ' => ?_⟩
  have hb1 := (GlobalTheory.T.theta_sum_tensor_product F κ κ φ hφ φ' hφ').1
  refine eq_of_theta hψ dd₁ (hd.maps _ hb1) (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (he.maps φ hφ) _ (h₂.maps φ' hφ')).1 fun w => ?_
  rw [← Matrix.fromCols_toCols w]
  generalize w.toCols₁ = u
  generalize w.toCols₂ = u'
  have m1 := rho_mem hψ d u hφ
  have m2 := rho_mem hψ (negD d) u' hφ'
  rw [← hd.Heisenberg₂ _ _ hb1, Ht _ (rho_mem hψ dd _ hb1), rho_box h, rho_box h₁, (GlobalTheory.T.theta_sum_tensor_product F κ κ _ m1 _ m2).2,
    ← he.Heisenberg₂ u φ hφ, ← h₂.Heisenberg₂ u' φ' hφ', (GlobalTheory.T.theta_sum_tensor_product F κ κ _ (he.maps _ m1) _ (h₂.maps _ m2)).2, Ha _ m1,
    LinearMap.smul_apply, thetaSum_smul, Hb _ m2]
  field_simp

end Dbl

end PositivityTheory.ThKF0

end
