import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cAsec

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cA_hasDeriv (x : Bool × B.Mat k r) {F : B.Mat k r → E} {g : B.Mat k r} (hd : DifferentiableAt ℝ F g) :
    HasDerivAt (fun t : ℝ => F (crv x g t)) (fderiv ℝ F g (dirv x g)) 0 :=
  hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (crv_hasDerivAt x g) (crv_zero x g).symm

theorem cA_Dx_eq (x : Bool × B.Mat k r) {F : B.Mat k r → E} (hd : Differentiable ℝ F) :
    Dx x F = fun g => fderiv ℝ F g (dirL x g) := by
  funext g
  rw [Dx_eq, dirL_apply]
  exact (cA_hasDeriv x (hd g)).deriv

theorem cA_Dx_smooth (x : Bool × B.Mat k r) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dx x F) := by
  rw [cA_Dx_eq x (hF.differentiable (by simp))]
  exact (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply (dirL x).contDiff

theorem cA_Dx_lin (x : Bool × B.Mat k r) {F₁ F₂ : B.Mat k r → E} (h₁ : Differentiable ℝ F₁)
    (h₂ : Differentiable ℝ F₂) (c : ℂ) :
    Dx x (fun g => F₁ g + c • F₂ g) = fun g => Dx x F₁ g + c • Dx x F₂ g := by
  funext g
  rw [Dx_eq, Dx_eq, Dx_eq, (cA_hasDeriv x (h₁ g)).deriv, (cA_hasDeriv x (h₂ g)).deriv]
  exact ((cA_hasDeriv x (h₁ g)).add ((cA_hasDeriv x (h₂ g)).const_smul c)).deriv

def Dwl (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E) : B.Mat k r → E :=
  w.foldr (fun x G => fun g => Dx x G g + lam x • G g) F

theorem cA_Dwl_smooth (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dwl lam w F) := by
  induction w with
  | nil => exact hF
  | cons x w ih => exact (cA_Dx_smooth x ih).add (ih.const_smul (lam x))

theorem cA_Dwl_lin (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F₁ F₂ : B.Mat k r → E}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁) (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂) (c : ℂ) :
    Dwl lam w (fun g => F₁ g + c • F₂ g) = fun g => Dwl lam w F₁ g + c • Dwl lam w F₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have d₁ := (cA_Dwl_smooth lam w h₁).differentiable (by simp)
    have d₂ := (cA_Dwl_smooth lam w h₂).differentiable (by simp)
    show (fun g => Dx x (Dwl lam w _) g + lam x • Dwl lam w _ g) = _
    rw [ih, cA_Dx_lin x d₁ d₂ c]
    funext g
    show _ = (Dx x (Dwl lam w F₁) g + lam x • Dwl lam w F₁ g) + c • (Dx x (Dwl lam w F₂) g + lam x • Dwl lam w F₂ g)
    rw [smul_add, smul_add, smul_comm c (lam x)]
    exact add_add_add_comm _ _ _ _

theorem cA_Dwl_append (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r)
    (F : B.Mat k r → E) : Dwl lam (w ++ [x]) F = Dwl lam w (fun g => Dx x F g + lam x • F g) := by
  simp [Dwl, List.foldr_append]

theorem cA_Dwl_bound (lam : Bool × B.Mat k r → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (g : B.Mat k r) (M : ℝ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ‖lam x‖ ≤ Λ) → (∀ s : List (Bool × B.Mat k r), s.Sublist w → ‖Dw s F g‖ ≤ M) →
      ‖Dwl lam w F g‖ ≤ (1 + Λ) ^ w.length * M := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro F _ _ hM
    simpa [Dwl, Dw] using hM [] (List.Sublist.refl _)
  | append_singleton w x ih =>
    intro F hF hl hM
    have hl' : ∀ y ∈ w, ‖lam y‖ ≤ Λ := fun y hy => hl y (by simp [hy])
    have hx : ‖lam x‖ ≤ Λ := hl x (by simp)
    rw [cA_Dwl_append, cA_Dwl_lin lam w (cA_Dx_smooth x hF) hF]
    have b1 := ih (Dx x F) (cA_Dx_smooth x hF) hl' (by
      intro s hs
      have := hM (s ++ [x]) (hs.append (List.Sublist.refl _))
      rwa [Dw_append] at this)
    have b2 := ih F hF hl' (fun s hs => hM s (hs.trans (List.sublist_append_left _ _)))
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM [] (List.nil_sublist _))
    calc ‖Dwl lam w (Dx x F) g + lam x • Dwl lam w F g‖
        ≤ (1 + Λ) ^ w.length * M + Λ * ((1 + Λ) ^ w.length * M) := by
          refine (norm_add_le _ _).trans (add_le_add b1 ?_)
          rw [norm_smul]
          exact mul_le_mul hx b2 (norm_nonneg _) hΛ
      _ = (1 + Λ) ^ (w ++ [x]).length * M := by simp [pow_succ]; ring

theorem cA_Dw_expmul (lam : Bool × B.Mat k r → ℂ) (h : B.Mat k r → ℂ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ∀ g (t : ℝ), h (crv x g t) = Complex.exp ((t : ℂ) * lam x) * h g) →
      Dw w (fun g => h g • F g) = fun g => h g • Dwl lam w F g := by
  intro w
  induction w with
  | nil => intro F _ _; rfl
  | cons x w ih =>
    intro F hF hh
    have hh' : ∀ y ∈ w, ∀ g (t : ℝ), h (crv y g t) = Complex.exp ((t : ℂ) * lam y) * h g :=
      fun y hy => hh y (by simp [hy])
    show Dx x (Dw w _) = _
    rw [ih F hF hh']
    funext g
    have hG := cA_Dwl_smooth lam w hF
    have d := cA_hasDeriv x ((hG.differentiable (by simp)) g)
    have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * lam x) * h g) (lam x * h g) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam x) (1 * lam x) 0 :=
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (lam x)
      have h2 := (h1.cexp).mul_const (h g)
      simpa using h2
    have hs : HasDerivAt (fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t))
        ((Complex.exp (((0 : ℝ) : ℂ) * lam x) * h g) • fderiv ℝ (Dwl lam w F) g (dirv x g) +
          (lam x * h g) • Dwl lam w F (crv x g 0)) 0 := he.smul d
    rw [Dx_eq]
    have e : (fun t : ℝ => h (crv x g t) • Dwl lam w F (crv x g t)) =
        fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t) := by
      funext t; rw [hh x (by simp) g t]
    rw [e, hs.deriv, crv_zero, ← dirL_apply, ← congrFun (cA_Dx_eq x (hG.differentiable (by simp))) g]
    show _ = h g • (Dx x (Dwl lam w F) g + lam x • Dwl lam w F g)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, smul_add, smul_smul]
    rw [mul_comm (lam x)]

theorem cA_Dw_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E')
    {U : Set (B.Mat k r)} (hU : IsOpen U) (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) U f) :
    ∀ g ∈ B.GV k r, g ∈ U → Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _ _; rfl
  | cons x w ih =>
    intro g hg hgU
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr_loc hx hU (f₂ := fun h => L (Dw w f h)) (ih hw' (sCkOn_mono hle hf)) g hg hgU]
    have hc : B.CkOn 1 U (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hgU hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

end cAsec

end PI.UnitaryCorollaryDerivatives
