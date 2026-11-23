import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeylCellAction

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def lmul (M : Mx k r) : Mx k r →L[ℝ] Mx k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ M)

theorem lmul_apply (M x : Mx k r) : lmul M x = M * x := by
  simp [lmul]

theorem lmul_coe (M : Mx k r) : (⇑(lmul M) : Mx k r → Mx k r) = fun x => M * x := funext (lmul_apply M)

theorem cont_lmul (M : Mx k r) : Continuous fun x : Mx k r => M * x := by
  rw [← lmul_coe]; exact (lmul M).continuous

section transl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eH_left (M : Mx k r) (p q : Fin (2 * r + k + 1)) (f : Mx k r → E) (g : Mx k r) :
    EH k r p q (fun x => f (M * x)) g = EH k r p q f (M * g) := by
  show EabH _ _ _ _ _ = EabH _ _ _ _ _
  simp only [EabH, RdV, Matrix.mul_assoc]

theorem smooth_left {i j : Fin (r + 1)} {D : Set (Mx k r)} {f : Mx k r → E} (M : Mx k r)
    (hM : ∀ x ∈ Glev k r i, M * x ∈ Glev k r j) (hf : SmoothLev k r j D f) :
    SmoothLev k r i {x | M * x ∈ D} (fun x => f (M * x)) := by
  intro x₀ hx₀
  obtain ⟨U, F, hU, hx₀U, hF, hFU⟩ := hf (M * x₀) ⟨hM x₀ hx₀.1, hx₀.2⟩
  have hc : Continuous fun x : Mx k r => M * x := cont_lmul M
  refine ⟨(fun x => M * x) ⁻¹' U, fun x => F (M * x), hU.preimage hc, hx₀U, ?_, ?_⟩
  · have hl : ContDiff ℝ ∞ fun x : Mx k r => M * x := by
      rw [← lmul_coe]; exact (lmul M).contDiff
    exact hF.comp hl.contDiffOn (fun x hx => hx)
  · intro g hg hgl
    exact hFU _ hg (hM g hgl)

end transl

theorem zero_le' (i : Fin (r + 1)) : (0 : Fin (r + 1)) ≤ i := by
  rw [Fin.le_def]; simp

theorem glev0 {g : Mx k r} (hg : g ∈ Glev k r 0) {i : Fin (r + 1)} {x : Mx k r} (hx : x ∈ Glev k r i) :
    g * x ∈ Glev k r 0 :=
  glev_mul hg (glev_mono (zero_le' i) hx)

theorem weyl_cell_mulVec_basis (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c *ᵥ bvec q = dd k l c q • bvec (sw k l q) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul, w1_apply]

theorem head_comm (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = n →
    wCell k r i c ∈ Glev k r 0 ∧ ∀ j : Fin (r + 1), i ≤ j → ∀ x ∈ Glev k r j, wCell k r i c * x = x * wCell k r i c
  | 0, i, hi => by
    have : i = 0 := Fin.ext (by simp [hi])
    subst this
    rw [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact ⟨glev_one _, fun _ _ x _ => by simp⟩
  | n + 1, i, hi => by
    have hl : n < r := by have := i.isLt; omega
    set l : Fin r := ⟨n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi])
    subst hil
    obtain ⟨ih0, ihc⟩ := head_comm c hc n l.castSucc (by simp [l])
    have hw := Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)
    rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ⟨glev_mul ih0 (glev_mono (zero_le' _) hw.1), fun j hj x hx => ?_⟩
    have hx1 : x ∈ Glev k r l.succ := glev_mono hj hx
    have hxc : x ∈ Glev k r j := hx
    have hcj : l.castSucc ≤ j := le_trans (by rw [Fin.le_def]; simp) hj
    rw [Matrix.mul_assoc, (hw.2 x hx1).2.1, ← Matrix.mul_assoc, ihc j hcj x hxc, Matrix.mul_assoc]

theorem tail (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (b : Fin r) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
    ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
      (∀ a : Fin r, b.val < a.val →
        T *ᵥ bvec (eI k r a) = if a.val < i.val then c a • bvec (esI k r a) else bvec (eI k r a)) ∧
      (∀ a : Fin r, i.val ≤ a.val → T *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
      (∀ c' : Fin r → ℂ, (∀ a : Fin r, b.val < a.val → c' a = c a) → wCell k r i c' = wCell k r b.succ c' * T)
  | 0, i, hi => by
    have : i = b.succ := Fin.ext (by simp [hi])
    subst this
    refine ⟨1, by simp, glev_one _, fun a ha => ?_, fun a _ => by simp, fun c' _ => by simp⟩
    rw [if_neg (by simp; omega)]
    simp
  | n + 1, i, hi => by
    have hl : b.val + 1 + n < r := by have := i.isLt; omega
    set l : Fin r := ⟨b.val + 1 + n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi]; omega)
    subst hil
    obtain ⟨T, hT, hTG, hTe, hTs, hTc⟩ := tail c hc b n l.castSucc (by simp [l])
    have hw := (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)).1
    refine ⟨T * w1 k r l (c l), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
    · exact glev_mul hTG (glev_mono (by rw [Fin.le_def]; simp [l]) hw)
    · intro a ha
      rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
      by_cases hal : a = l
      · subst hal
        rw [sw_e, dd_e, Matrix.mulVec_smul, hTs _ (by simp [l]), if_pos (by simp [l])]
      · have hav : a.val ≠ l.val := fun h => hal (Fin.ext h)
        have h1 : eI k r a ≠ eI k r l := by simp [eI, Fin.ext_iff]; exact hav
        have h2 : eI k r a ≠ esI k r l := by simp [eI, esI, Fin.ext_iff]; have := l.isLt; omega
        rw [sw_o l h1 h2, dd_o l _ h1 h2, one_smul, hTe a ha]
        have hiff : a.val < (l.castSucc : Fin (r + 1)).val ↔ a.val < (l.succ : Fin (r + 1)).val := by
          simp only [Fin.val_castSucc, Fin.val_succ]; omega
        by_cases h3 : a.val < (l.castSucc : Fin (r + 1)).val
        · rw [if_pos h3, if_pos (hiff.1 h3)]
        · rw [if_neg h3, if_neg (fun h => h3 (hiff.2 h))]
    · intro a ha
      rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
      have hal : l.val < a.val := by simp at ha; omega
      have h1 : esI k r a ≠ eI k r l := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
      have h2 : esI k r a ≠ esI k r l := by simp [esI, Fin.ext_iff]; have := a.isLt; omega
      rw [sw_o l h1 h2, dd_o l _ h1 h2, one_smul, hTs a (by simp at ha ⊢; omega)]
    · intro c' hc'
      rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hTc c' hc', hc' l (by simp [l]; omega), Matrix.mul_assoc]

theorem cd_wCell : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = n →
    ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => wCell k r i c) (OmX r)
  | 0, i, hi => by
    have : i = 0 := Fin.ext (by simp [hi])
    subst this
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact contDiffOn_const
  | n + 1, i, hi => by
    have hl : n < r := by have := i.isLt; omega
    set l : Fin r := ⟨n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi])
    subst hil
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    exact Formalism.FourierDecayAlt.P.Qx6.cd_matmul (cd_wCell n l.castSucc (by simp [l])) (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l)

section diff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem diff_comp {D : Set (Mx k r)} {f : Mx k r → E} (hS : SmoothLev k r 0 D f) {φ : (Fin r → ℂ) → Mx k r}
    (hφ : ContDiffOn ℝ ∞ φ (OmX r)) (hφG : ∀ c ∈ OmX r, φ c ∈ Glev k r 0) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (hcD : φ c ∈ D) : DifferentiableAt ℝ (fun c' => f (φ c')) c := by
  obtain ⟨U, F, hU, hcU, hF, hFU⟩ := hS (φ c) ⟨hφG c hc, hcD⟩
  have hO : IsOpen (OmX r) := Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r
  have hN : IsOpen (OmX r ∩ φ ⁻¹' U) := hφ.continuousOn.isOpen_inter_preimage hO hU
  have hev : (fun c' => f (φ c')) =ᶠ[nhds c] fun c' => F (φ c') := by
    filter_upwards [hN.mem_nhds ⟨hc, hcU⟩] with c' hc'
    exact hFU _ hc'.2 (hφG c' hc'.1)
  have hd : DifferentiableAt ℝ (fun c' => F (φ c')) c := by
    have h1 : ContDiffAt ℝ ∞ F (φ c) := hF.contDiffAt (hU.mem_nhds hcU)
    have h2 : ContDiffAt ℝ ∞ φ c := hφ.contDiffAt (hO.mem_nhds hc)
    exact (h1.comp c h2).differentiableAt (by simp)
  exact hd.congr_of_eventuallyEq hev

theorem fderiv_line {F₁ F₂ : (Fin r → ℂ) → E} {c v : Fin r → ℂ} (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ t : ℝ, F₁ (c + t • v) = F₂ (c + t • v)) :
    fderiv ℝ F₁ c v = fderiv ℝ F₂ c v := by
  have hγ : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  have e1 := h₁.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have e2 := h₂.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hfun : (F₁ ∘ fun t : ℝ => c + t • v) = F₂ ∘ fun t : ℝ => c + t • v := funext fun t => h t
  rw [hfun] at e1
  exact e1.unique e2

theorem pOp_line {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ c' : Fin r → ℂ, (∀ a, a ≠ l → c' a = c a) → F₁ c' = F₂ c') :
    pOp l F₁ c = pOp l F₂ c := by
  have hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w) := fun w =>
    fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]
  simp only [pOp, wirt, hv]

end diff

end Formalism.FourierDecayAlt.P.WeylCellAction

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem right_rule_derivative : PBN.RightRuleE := by
  intro E _ _ k r z' D f hz' hD hS hR g hg a b hab
  have hb := b.isLt
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r a.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' a {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).1
  have hjlt : b.val - a.val - 1 < mdim k r a.succ := by simp [mdim]; omega
  have hpos : posL k r a.succ ⟨b.val - a.val - 1, hjlt⟩ = eI k r b := by
    simp [posL, eI, Fin.ext_iff]; omega
  have h := hrule ⟨b.val - a.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  congr 1
  have ha1 : (a.succ : Fin (r + 1)).val < r := by simp; omega
  simp only [xv, fvec, hpos, Fin.val_succ]
  rw [dif_pos (show a.val + 1 < r by omega)]
  by_cases hh : b.val = a.val + 1
  · simp [hh, bvec, eI]
  · simp [hh, bvec, eI, Fin.ext_iff]

theorem left_rule_cell : PBN.LeftRuleCell := by
  intro E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba
  have ha := a.isLt
  have hcne : ∀ l, c l ≠ 0 := hc
  obtain ⟨hW0, hWcomm⟩ := head_comm (k := k) c hcne b.val b.castSucc (by simp)
  obtain ⟨T, hT, hTG, hTe, -, -⟩ := tail (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).1
  have hjlt : a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨a.val - b.val - 1, hjlt⟩ = eI k r a := by
    simp [posL, eI, Fin.ext_iff]; omega
  have h := hrule ⟨a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [if_pos (by simp)] at hTa
  have hy : ybv k r z b.succ (T * g) ⟨a.val - b.val - 1, hjlt⟩ = if a.val = b.val + 1 then c a else 0 := by
    simp only [ybv, hpos, fvec, dif_pos hb1]
    rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI, ← Matrix.mulVec_mulVec, hga, hTa]
    simp only [Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, esI, Fin.ext_iff, Fin.val_succ]
    by_cases hh : a.val = b.val + 1
    · simp [hh]
    · rw [if_neg, if_neg hh, mul_zero]
      have := a.isLt; omega
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [if_pos hh, if_pos hh, div_eq_inv_mul]
  · rw [if_neg hh, if_neg hh, mul_zero]

theorem torus_cell : PBN.TorusCell := by
  intro E _ _ k r D f hD hS c hc g hg hWD l
  have hcne : ∀ a, c a ≠ 0 := hc
  have hl := l.isLt
  obtain ⟨hW0, -⟩ := head_comm (k := k) c hcne l.val l.castSucc (by simp)
  obtain ⟨T, hT, hTG, -, -, hTc⟩ := tail (k := k) c hcne l (r - l.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r l.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r l.castSucc c * (w1 k r l (c l) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r l.castSucc, wCell k r l.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r l.castSucc c) hWx hS
  have hD' : IsOpen {x : Mx k r | wCell k r l.castSucc c * x ∈ D} := hD.preimage (cont_lmul _)
  have hpt : w1 k r l (c l) * (T * g) ∈ {x | wCell k r l.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.torus_action_rule E k r l {x | wCell k r l.castSucc c * x ∈ D}
    (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).1
  rw [eH_left, ← hsplit] at hrule
  rw [hrule]
  have hG : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' ∈ Glev k r 0 := fun c' hc' =>
    (head_comm (k := k) c' hc' r (Fin.last r) (by simp)).1
  have hd₂ : DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c := by
    refine diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g)
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (cd_wCell r (Fin.last r) (by simp)) contDiffOn_const)
      (fun c' hc' => glev_mul (hG c' hc') (glev_mono (zero_le' _) hg)) hc hWD
  have hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c := by
    refine diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const
        (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) hc ?_
    · refine glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1)
        (glev_mono (zero_le' _) hg₁))
    · rw [← hsplit]; exact hWD
  refine pOp_line l hd₁ hd₂ fun c' hc' => ?_
  have hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c :=
    Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)
  have hup := hTc c' fun a ha => hc' a (fun h => by subst h; omega)
  show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)
  rw [hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P
