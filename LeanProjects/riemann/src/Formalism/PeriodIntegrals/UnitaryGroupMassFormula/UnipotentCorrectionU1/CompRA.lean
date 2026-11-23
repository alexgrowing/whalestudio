import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CRH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma dif {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

lemma hd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  rw [Dx_eq]
  exact ((hf _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).differentiableAt.hasDerivAt

lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  have h := (hf (crv x g 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  rw [crv_zero] at h
  rw [dirL_apply]
  exact (hd_Dx x hf g).unique h

lemma cd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (dif hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

lemma cd_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact cd_Dx x ih

lemma Dx_add' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  funext g
  exact (hd_Dx x (ha.add hb) g).unique ((hd_Dx x ha g).add (hd_Dx x hb g))

lemma Dw_add' (w : List (Bool × Mat k r)) {a b : Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = _
    rw [ih]
    exact Dx_add' x (dif (cd_Dw w ha)) (dif (cd_Dw w hb))

lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hd_Dx x ha g).mul (hd_Dx x hb g)
  rw [h0] at h
  exact (hd_Dx x (ha.mul hb) g).unique h

def Spl (w w₁ w₂ : List (Bool × Mat k r)) : Prop := w₁.Sublist w ∧ w₂.Sublist w ∧ (w₁ ++ w₂).Perm w

private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibB (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ a b : Mat k r → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb hM
    simpa [Dw, norm_mul] using hM [] [] (by unfold Spl; simp)
  | append_singleton w x ih =>
    intro a b ha hb hM
    rw [Dw_append_singleton, Dx_mul' x (dif ha) (dif hb),
      Dw_add' w ((cd_Dx x ha).mul hb) (ha.mul (cd_Dx x hb))]
    have h1 := ih (Dx x a) b (cd_Dx x ha) hb (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (by
        unfold Spl
        exact ⟨s1.append (List.Sublist.refl _), s2.trans (List.sublist_append_left _ _), hp⟩)
      rwa [Dw_append_singleton] at this)
    have h2 := ih a (Dx x b) ha (cd_Dx x hb) (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (by
        unfold Spl
        exact ⟨s1.trans (List.sublist_append_left _ _), s2.append (List.Sublist.refl _), hp⟩)
      rwa [Dw_append_singleton] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

end PI.UnitaryCorollaryDerivatives.CRH
