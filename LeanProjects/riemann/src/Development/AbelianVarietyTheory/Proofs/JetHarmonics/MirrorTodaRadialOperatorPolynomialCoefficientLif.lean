import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHeadV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.MirrorToda

section rules

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}

theorem left_star (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz : inWb k r z)
    (hD : IsOpen D) (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (hS : SmoothLev k r 0 D f)
    (hL : LeftEq k r z 0 D f) (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (a b : Fin r) (hba : b.val < a.val) :
    EH k r (esI k r b) (esI k r a) f (wCell k r (Fin.last r) c * g) =
      (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • f (wCell k r (Fin.last r) c * g) := by
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
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [if_pos (by simp)] at hTa
  have hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ =
      star (if a.val = b.val + 1 then c a else 0) := by
    simp only [yv, hpos, fvec, dif_pos hb1]
    obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.xi_Y_zhat_identity k r z z (T * g) ⟨_, hb1⟩ a hg₁.1
    rw [h2, ← h1]
    congr 1
    rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI, ← Matrix.mulVec_mulVec, hga, hTa]
    simp only [Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, esI, Fin.ext_iff, Fin.val_succ]
    by_cases hh : a.val = b.val + 1
    · simp [hh]
    · rw [if_neg, if_neg hh, mul_zero]
      have := a.isLt; omega
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [if_pos hh, if_pos hh, div_eq_inv_mul]
  · rw [if_neg hh, if_neg hh, star_zero, mul_zero]

theorem pbOp_line {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ c' : Fin r → ℂ, (∀ a, a ≠ l → c' a = c a) → F₁ c' = F₂ c') :
    pbOp l F₁ c = pbOp l F₂ c := by
  have hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w) := fun w =>
    fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]
  simp only [pbOp, wirtBar, hv]

theorem wCell_glev {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    wCell k r (Fin.last r) c * g ∈ Glev k r 0 :=
  glev_mul (head_comm (k := k) c hc r (Fin.last r) (by simp)).1 (glev_mono (zero_le' _) hg)

theorem diff_cell {D : Set (Mx k r)} {f : Mx k r → E} (hS : SmoothLev k r 0 D f) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hWD : wCell k r (Fin.last r) c * g ∈ D) :
    DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c :=
  diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g)
    (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (cd_wCell r (Fin.last r) (by simp)) contDiffOn_const)
    (fun _ hc' => wCell_glev hc' hg) hc hWD

theorem torus_star (D : Set (Mx k r)) (f : Mx k r → E) (hD : IsOpen D) (hS : SmoothLev k r 0 D f)
    (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (l : Fin r) :
    EH k r (esI k r l) (esI k r l) f (wCell k r (Fin.last r) c * g) =
      -pbOp l (fun c' => f (wCell k r (Fin.last r) c' * g)) c := by
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
    (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).2
  rw [eH_left, ← hsplit] at hrule
  rw [hrule]
  congr 1
  have hd₂ := diff_cell hS hc hg hWD
  have hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c := by
    refine diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const
        (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) hc ?_
    · refine glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1)
        (glev_mono (zero_le' _) hg₁))
    · rw [← hsplit]; exact hWD
  refine pbOp_line l hd₁ hd₂ fun c' hc' => ?_
  have hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c :=
    Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)
  have hup := hTc c' fun a ha => hc' a (fun h => by subst h; omega)
  show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)
  rw [hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]

theorem gauge_bar (n : Fin r → ℕ) (H : (Fin r → ℂ) → E) (c : Fin r → ℂ) (hc : c ∈ OmX r)
    (hH : DifferentiableAt ℝ H c) (l : Fin r) :
    pbOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pbOp l H c + ((n l : ℂ) / 2) • H c) := by
  have hγ : DifferentiableAt ℝ (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ)) c := by
    have e : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ)) =
        fun c' => ∏ a, ((‖c' a‖ ^ n a : ℝ) : ℂ) := by
      funext c'; push_cast; rfl
    rw [e]
    have h : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => ∏ a, ((‖c' a‖ ^ n a : ℝ) : ℂ)) (OmX r) :=
      contDiffOn_prod (fun a _ => Formalism.FourierDecayAlt.P.Qx6.cd_gamma a (n a))
    exact (h.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hγl := Formalism.FourierDecayAlt.P.Qx6.diff_gamma l (n l) hc
  have hsplit : ∀ c' : Fin r → ℂ, ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) =
      ((∏ a ∈ Finset.univ.erase l, ‖c' a‖ ^ n a : ℝ) : ℂ) * ((‖c' l‖ ^ n l : ℝ) : ℂ) := by
    intro c'
    rw [← Complex.ofReal_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  have h := Formalism.FourierDecayAlt.P.Qx6.opL_dir l 3 (f₁ := fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c')
    (f₂ := fun c' => ((‖c' l‖ ^ n l : ℝ) : ℂ) • H c') (c := c)
    ((∏ a ∈ Finset.univ.erase l, ‖c a‖ ^ n a : ℝ) : ℂ) (hγ.smul hH) (hγl.smul hH)
    (Filter.Eventually.of_forall fun s => by
      rw [hsplit, smul_smul]
      congr 3
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)])
  change pbOp l _ c = _ • pbOp l _ c at h
  rw [h, Formalism.FourierDecayAlt.P.Qx6.pbOp_smul l hc hγl hH, Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma l hc, hsplit]
  module

theorem wCell_vec (c : Fin r → ℂ) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = n →
    (∀ a : Fin r, i.val ≤ a.val → wCell k r i c *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧
    (∀ a : Fin r, a.val < i.val → wCell k r i c *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a))
  | 0, i, hi => by
    have : i = 0 := Fin.ext (by simp [hi])
    subst this
    rw [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact ⟨fun a _ => by simp, fun a ha => absurd ha (by simp)⟩
  | n + 1, i, hi => by
    have hl : n < r := by have := i.isLt; omega
    set l : Fin r := ⟨n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi])
    subst hil
    obtain ⟨ih1, ih2⟩ := wCell_vec c n l.castSucc (by simp [l])
    rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
      have hal : l.val < a.val := by simp at ha; omega
      have h1 : eI k r a ≠ eI k r l := by simp [eI, Fin.ext_iff]; omega
      have h2 : eI k r a ≠ esI k r l := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
      rw [sw_o l h1 h2, dd_o l _ h1 h2, one_smul, ih1 a (by simp; omega)]
    · rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
      by_cases hal : a = l
      · subst hal
        rw [sw_es, dd_es, Matrix.mulVec_smul, ih1 _ (by simp)]
      · have hav : a.val ≠ l.val := fun h => hal (Fin.ext h)
        have h1 : esI k r a ≠ eI k r l := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
        have h2 : esI k r a ≠ esI k r l := by simp [esI, Fin.ext_iff]; have := a.isLt; have := l.isLt; omega
        rw [sw_o l h1 h2, dd_o l _ h1 h2, one_smul, ih2 a (by simp at ha ⊢; omega)]

theorem cell_inv_vec {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (a : Fin r) :
    (wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have h1 : (wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, (hg.2 a (by simp)).2,
      (wCell_vec (k := k) c r (Fin.last r) (by simp)).2 a (by simp), smul_smul,
      mul_inv_cancel₀ (star_ne_zero.2 (hc a)), one_smul]
  have hU := (wCell_glev hc hg).1
  have h2 : (wCell k r (Fin.last r) c * g)⁻¹ * (wCell k r (Fin.last r) c * g) = 1 :=
    (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hU).2
  rw [← h1, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

end rules

section radial

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def tvp {A : Type} [Ring A] [Algebra ℂ A] (L : R.LevelData A r) (Y : ℂ) (m : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.ofFn (L.Tvl Y)).take m).reverse).prod

theorem tvp_succ {A : Type} [Ring A] [Algebra ℂ A] (L : R.LevelData A r) (Y : ℂ) (m : ℕ) (h : m < r) :
    tvp L Y (m + 1) = L.Tvl Y ⟨m, h⟩ * tvp L Y m := by
  unfold tvp
  rw [List.take_succ_eq_append_getElem (by simpa using h)]
  simp

theorem mirrorTodaTransferPartialProduct_succ_apply_zero_zero {A : Type} [Ring A] [Algebra ℂ A] (L : R.LevelData A r) (Y : ℂ) (m : ℕ) (h : m < r) :
    tvp L Y (m + 1) 0 0 = (algebraMap ℂ A Y - L.pb ⟨m, h⟩) * tvp L Y m 0 0 - L.cb ⟨m, h⟩ * tvp L Y m 1 0 := by
  rw [tvp_succ L Y m h]
  simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl, sub_eq_add_neg]

theorem mirrorTodaTransferPartialProduct_succ_apply_one_zero {A : Type} [Ring A] [Algebra ℂ A] (L : R.LevelData A r) (Y : ℂ) (m : ℕ) (h : m < r) :
    tvp L Y (m + 1) 1 0 = L.cbi ⟨m, h⟩ * tvp L Y m 0 0 := by
  rw [tvp_succ L Y m h]
  simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]

theorem radial_chain (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hX : IsActualLevel X L) (Y : ℂ) (Φ : RadSp k r z z' π π') (g : Mx k r)
    (G : ℕ → (Fin r → ℂ) → (Wq →L[ℂ] Wp))
    (h0 : ∀ c ∈ OmX r, (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = G 0 c)
    (h1 : ∀ h : 0 < r, ∀ c ∈ OmX r, G 1 c = Y • G 0 c - pbOp ⟨0, h⟩ (G 0) c)
    (h2 : ∀ (m : ℕ) (h : m + 1 < r), ∀ c ∈ OmX r, G (m + 2) c = Y • G (m + 1) c - pbOp ⟨m + 1, h⟩ (G (m + 1)) c -
      (star (c ⟨m + 1, h⟩) / star (c ⟨m, by omega⟩)) • G m c) :
    ∀ c ∈ OmX r, (((L.Avr Y).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = G r c := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hX
  have e00 : ∀ (m : ℕ) (h : m < r), ∀ c ∈ OmX r,
      (∀ c ∈ OmX r, (((tvp L Y m 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = G m c) →
      (((tvp L Y (m + 1) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        Y • G m c - pbOp ⟨m, h⟩ (G m) c -
          star (c ⟨m, h⟩) • (((tvp L Y m 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g := by
    intro m h c hc ih
    rw [mirrorTodaTransferPartialProduct_succ_apply_zero_zero L Y m h, hpb, hcb]
    change ((Y • (tvp L Y m 0 0).1 Φ - X.op ⟨m, h⟩ 3 ((tvp L Y m 0 0).1 Φ) -
      X.op ⟨m, h⟩ 4 ((tvp L Y m 1 0).1 Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = _
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, X.op_apply]
    rw [ih c hc]
    congr 2
    refine Formalism.FourierDecayAlt.P.Qx6.opL_germ ⟨m, h⟩ 3 ?_
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc'
    exact ih c' hc'
  have e10 : ∀ (m : ℕ) (h : m < r) (c : Fin r → ℂ),
      (((tvp L Y (m + 1) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        (star (c ⟨m, h⟩))⁻¹ • (((tvp L Y m 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g := by
    intro m h c
    rw [mirrorTodaTransferPartialProduct_succ_apply_one_zero L Y m h, hcbi]
    change ((X.op ⟨m, h⟩ 5 ((tvp L Y m 0 0).1 Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = _
    rw [X.op_apply]
    rfl
  have b0 : ∀ c ∈ OmX r, (((tvp L Y 0 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = G 0 c := by
    intro c hc
    have : tvp L Y 0 0 0 = 1 := by simp [tvp]
    rw [this]
    exact h0 c hc
  have key : ∀ m : ℕ, m ≤ r →
      (∀ c ∈ OmX r, (((tvp L Y m 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = G m c) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => intro _; exact b0
    | one =>
      intro h c hc
      have : tvp L Y 0 1 0 = 0 := by simp [tvp]
      rw [e00 0 h c hc b0, h1 h c hc, this]
      change _ - star (c ⟨0, h⟩) • (0 : Wq →L[ℂ] Wp) = _
      rw [smul_zero, sub_zero]
    | more m ih0 ih1 =>
      intro h c hc
      rw [e00 (m + 1) h c hc (ih1 (by omega)), e10 m (by omega), ih0 (by omega) c hc, h2 m h c hc, smul_smul,
        div_eq_mul_inv]
  have : L.Avr Y = tvp L Y r 0 0 := by
    unfold R.LevelData.Avr R.LevelData.Tvprod tvp
    rw [List.take_of_length_le (by simp)]
  rw [this]
  exact key r le_rfl

theorem drb_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hX : IsActualLevel X L) (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    ((L.Drb.1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      (∏ a, star (c a)) • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  obtain ⟨-, -, -, -, hcb, -⟩ := hX
  have key : ∀ l : List (Fin r), ((((l.map L.cb).prod).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      (l.map fun a => star (c a)).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [hcb]
      change ((X.op a 4 (((l.map L.cb).prod).1 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = _
      rw [X.op_apply, mul_smul, ← ih]
      rfl
  unfold R.LevelData.Drb
  rw [List.ofFn_eq_map, key, ← List.ofFn_eq_map, List.prod_ofFn]

end radial

section group

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC Formalism.FourierDecayAlt.C3
open Formalism.FourierDecayAlt.P.PBG (Emir ep rv)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {D : Set (Mx k r)}

def mq (hD : IsOpen D) (ℓ : ℂ) (m : ℕ) : SA E hD :=
  if h : m ≤ r then qminor (Emir (EA hD)) (xR k r m h) (xR k r m h) (-ℓ) else 0

theorem mirror_apply_block {A : Type} [Ring A] [Algebra ℂ A] (U : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (a b : Fin r) :
    Emir U (eI k r a) (eI k r b) = -(((-1 : ℂ) ^ a.val * (-1) ^ b.val) • U (esI k r b) (esI k r a)) := by
  unfold Emir
  rw [Formalism.FourierDecayAlt.P.PBG.rv_eI, Formalism.FourierDecayAlt.P.PBG.rv_eI]
  rfl

theorem tm_emir {A : Type} [Ring A] [Algebra ℂ A] (U : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ)
    (a : Fin r) : Tm (Emir U) u (eI k r a) (eI k r a) = algebraMap ℂ _ u - U (esI k r a) (esI k r a) := by
  unfold Tm
  rw [if_pos rfl, mirror_apply_block, ← mul_pow]
  simp [sub_eq_add_neg]

theorem chain_mirror {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
    (U : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hU : GlRel U) (Λ : A →ₗ[ℂ] M) (c : Fin r → ℂ)
    (hRR : ∀ (x : A) (a b : Fin r), a.val < b.val →
      Λ (x * U (esI k r b) (esI k r a)) = (if b.val = a.val + 1 then (1 : ℂ) else 0) • Λ x)
    (hLL : ∀ (x : A) (a b : Fin r), b.val < a.val →
      Λ (U (esI k r b) (esI k r a) * x) = (if a.val = b.val + 1 then c a / c b else 0) • Λ x)
    (u : ℂ) (m : ℕ) (h : m + 1 < r) :
    Λ (qminor (Emir U) (xR k r (m + 2) h) (xR k r (m + 2) h) u) =
      (u - ((m + 1 : ℕ) : ℂ)) • Λ (qminor (Emir U) (xR k r (m + 1) h.le) (xR k r (m + 1) h.le) u) -
        Λ (U (esI k r ⟨m + 1, h⟩) (esI k r ⟨m + 1, h⟩) *
          qminor (Emir U) (xR k r (m + 1) h.le) (xR k r (m + 1) h.le) u) -
        (c ⟨m + 1, h⟩ / c ⟨m, by omega⟩) •
          Λ (qminor (Emir U) (xR k r m (by omega)) (xR k r m (by omega)) u) := by
  have hG := Formalism.FourierDecayAlt.P.PBG.Emir_gl hU
  have main := chainX1' k r c (Emir U) Λ hG m h u
    (fun x l hl => by
      rw [mirror_apply_block, mul_neg, mul_smul_comm, map_neg, map_smul, hRR _ _ _ (by simp; omega), if_neg (by simp; omega)]
      simp)
    (fun x => by
      rw [mirror_apply_block, mul_neg, mul_smul_comm, map_neg, map_smul, hRR _ _ _ (by simp), if_pos (by simp)]
      simp only [pow_succ, ← mul_assoc, ← mul_pow]
      simp)
    (fun x q hq => by
      rw [mirror_apply_block, neg_mul, smul_mul_assoc, map_neg, map_smul, hLL _ _ _ (by simp; omega)]
      by_cases hqm : q = m
      · subst hqm
        rw [if_pos (by simp), if_pos rfl]
        have : ((-1 : ℂ) ^ (q + 1) * (-1) ^ q) = -1 := by
          rw [pow_succ, mul_right_comm, ← mul_pow]; simp
        simp only [this]
        simp
      · rw [if_neg (by simp; omega), if_neg hqm]
        simp)
  have hcomm := Formalism.FourierDecayAlt.P.CutHL.comm_qminor (Emir U) hG (xR k r (m + 1) h.le) (xR k r (m + 1) h.le)
    u (eI k r ⟨m + 1, h⟩) (fun i => by have := i.isLt; simp [xR, eI, Fin.ext_iff]; omega)
    (fun i => by have := i.isLt; simp [xR, eI, Fin.ext_iff]; omega)
  rw [mirror_apply_block, ← mul_pow] at hcomm
  simp only [neg_mul_neg, mul_one, one_pow, one_smul, Commute.neg_left_iff] at hcomm
  rw [tm_emir, mul_sub, ← hcomm.eq, ← Algebra.commutes, ← Algebra.smul_def, map_sub, map_smul] at main
  exact main

theorem mq_zero (hD : IsOpen D) (ℓ : ℂ) : mq (E := E) hD ℓ 0 = 1 := by
  unfold mq
  rw [dif_pos (Nat.zero_le r)]
  simp [qminor]

theorem mq_one (hD : IsOpen D) (ℓ : ℂ) (h : 0 < r) :
    mq (E := E) hD ℓ 1 = algebraMap ℂ _ (-ℓ) - EA hD (esI k r ⟨0, h⟩) (esI k r ⟨0, h⟩) := by
  unfold mq
  rw [dif_pos (show 1 ≤ r from h), ← tm_emir]
  simp only [qminor, Finset.univ_unique, Finset.sum_singleton, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  simp
  rfl

theorem la_torus (hD : IsOpen D) (v : VS k r 0 D E) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hW : wCell k r (Fin.last r) c * g ∈ D) (l : Fin r) (x : SA E hD) :
    La hD v (wCell k r (Fin.last r) c * g) (EA hD (esI k r l) (esI k r l) * x) =
      -pbOp l (fun c' => La hD v (wCell k r (Fin.last r) c' * g) x) c := by
  rw [La_apply]
  change ((Eh hD (cI (esI k r l)) (cI (esI k r l)) ((x : Module.End ℂ (VS k r 0 D E)) v) : VS k r 0 D E) :
    Mx k r → E) _ = _
  rw [ev_E hD _ _ _ ⟨wCell_glev hc hg, hW⟩, posL_cI]
  exact torus_star D _ hD ((x : Module.End ℂ (VS k r 0 D E)) v).2.1 c hc g hg hW l

theorem la_step (hD : IsOpen D) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J)
    (hL : LeftEq k r z 0 D J) (hR : RightEq k r z' 0 D J) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hW : wCell k r (Fin.last r) c * g ∈ D) (ℓ : ℂ) (m : ℕ) (h : m + 1 < r) :
    La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c * g) (mq hD ℓ (m + 2)) =
      (-ℓ - ((m + 1 : ℕ) : ℂ)) • La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c * g) (mq hD ℓ (m + 1)) +
        pbOp ⟨m + 1, h⟩ (fun c' => La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c' * g) (mq hD ℓ (m + 1))) c -
        (star (c ⟨m + 1, h⟩) / star (c ⟨m, by omega⟩)) •
          La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c * g) (mq hD ℓ m) := by
  set v := P.PBG.vK hD J hS with hv
  set W := wCell k r (Fin.last r) c * g with hWdef
  have hWG : W ∈ Glev k r 0 ∩ D := ⟨wCell_glev hc hg, hW⟩
  have hRule : ∀ g ∈ Glev k r 0 ∩ D, ∀ p q, InNp k r p q → EH k r p q J g = dpsiP k r z' p q • J g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' J g hz'
      (fun n hn => hR g hg n ⟨hn, hn.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩) p q hpq
  have hRR : ∀ (x : SA E hD) (a b : Fin r), a.val < b.val →
      La hD v W (x * EA hD (esI k r b) (esI k r a)) = (if b.val = a.val + 1 then (1 : ℂ) else 0) • La hD v W x := by
    intro x a b hab
    have hb := b.isLt
    have h1 := P.PBG.La_rule hD z' J hS hRule W (x : Module.End ℂ (VS k r 0 D E)) (esI k r b) (esI k r a)
      (by unfold InNp; simp only [esI]; omega)
    have h2 : dpsiP k r z' (esI k r b) (esI k r a) = if b.val = a.val + 1 then (1 : ℂ) else 0 := by
      unfold dpsiP
      have ea : (esI k r a).val = 2 * r + k - a.val := rfl
      have eb : (esI k r b).val = 2 * r + k - b.val := rfl
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      by_cases h : b.val = a.val + 1
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [h2] at h1
    exact h1
  have hvL : LeftEq k r z 0 D (v : Mx k r → E) := by
    intro x hx n hn
    have hnx : n * x ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hx.1, hDN x hx n hn⟩
    show cut k r 0 D J _ = _ • cut k r 0 D J _
    rw [cut_of_mem J hnx, cut_of_mem J hx]
    exact hL x hx n hn
  have hLL : ∀ (x : SA E hD) (a b : Fin r), b.val < a.val →
      La hD v W (EA hD (esI k r b) (esI k r a) * x) =
        (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • La hD v W x := by
    intro x a b hab
    rw [La_apply]
    change ((Eh hD (cI (esI k r b)) (cI (esI k r a)) ((x : Module.End ℂ (VS k r 0 D E)) v) : VS k r 0 D E) :
      Mx k r → E) _ = _
    rw [ev_E hD _ _ _ hWG, posL_cI, posL_cI]
    exact left_star z D _ hz hD hDN ((x : Module.End ℂ (VS k r 0 D E)) v).2.1 (leftEq_SA hD z hDN x v hvL)
      c hc g hg hW a b hab
  have main := chain_mirror (EA hD) (EA_gl (E := E) hD) (La hD v W) (fun a => star (c a)) hRR hLL (-ℓ) m h
  rw [la_torus hD v hg hc hW] at main
  unfold mq
  rw [dif_pos (show m + 2 ≤ r from h), dif_pos h.le, dif_pos (show m ≤ r by omega), main, sub_neg_eq_add]

end group

section cell

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC Formalism.FourierDecayAlt.C3
open Formalism.FourierDecayAlt.P.PBG (Emir ep rv)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {D : Set (Mx k r)}

theorem quantumMinor_mirror {A : Type} [Ring A] [Algebra ℂ A] (U : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (hU : GlRel U) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ) :
    ((-1 : ℂ) ^ m) • qminor (Emir U) (xR k r m hm) (xR k r m hm) (-ℓ) =
      qminor U (sR k r m hm) (sR k r m hm) (ℓ + (m : ℂ) - 1) := by
  rw [Formalism.FourierDecayAlt.P.PBG.qminor_Emir, Formalism.FourierDecayAlt.P.PBG.rv_xR, Formalism.FourierDecayAlt.P.PBG.prod_ep_sq, one_smul,
    duality hU (sR k r m hm) (sR k r m hm) (ℓ + (m : ℂ) - 1)]
  congr 2
  ring

theorem pbOp_csmul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (l : Fin r) {H : (Fin r → ℂ) → E}
    {c : Fin r → ℂ} (hH : DifferentiableAt ℝ H c) : pbOp l (fun c' => s • H c') c = s • pbOp l H c :=
  Formalism.FourierDecayAlt.P.Qx6.opL_dir l 3 s (hH.const_smul s) hH (Filter.Eventually.of_forall fun _ => rfl)

theorem aav_cell {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) {J : Mx k r → E}
    (hS : SmoothLev k r 0 D J) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hW : wCell k r (Fin.last r) c * g ∈ D) (ℓ : ℂ) :
    AAvop k r r le_rfl ℓ J (wCell k r (Fin.last r) c * g) = (∏ a, star (c a)) • (((-1 : ℂ) ^ r) •
      La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c * g) (mq hD ℓ r)) := by
  rw [← P.PBG.La_AAv hD J hS _ ⟨wCell_glev hc hg, hW⟩,
    Formalism.FourierDecayAlt.P.SignAntidiagonal.AAv_head k r _ _ r le_rfl (Matrix.diagonal c) ℓ, map_smul, Matrix.det_diagonal, star_prod,
    ← map_smul (La _ _ _)]
  · congr 1
    unfold mq
    rw [dif_pos le_rfl, quantumMinor_mirror _ (EA_gl hD), La_apply]
    have := map_qminor (SA E hD).val (EA hD) (sR k r r le_rfl) (sR k r r le_rfl) (ℓ + (r : ℂ) - 1)
    simp only [Subalgebra.coe_val] at this
    rw [this]
    rfl
  · intro a p _ hp
    show ((wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a)) p = 0
    rw [cell_inv_vec hc hg]
    have : p ≠ esI k r a := fun h => hp ⟨a, h.symm⟩
    simp [bvec, this]
  · intro a b
    show ((wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a)) (esI k r b) = _
    rw [cell_inv_vec hc hg]
    by_cases h : a = b
    · subst h; simp [bvec]
    · have : esI k r b ≠ esI k r a := by
        have := a.isLt; have := b.isLt
        have : a.val ≠ b.val := fun e => h (Fin.ext e)
        simp [esI, Fin.ext_iff]; omega
      simp [bvec, this, Matrix.diagonal_apply_ne _ h]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem cell_radial (hD : IsOpen D) (hz : inWb k r z) (hz' : inWb k r z')
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hS : SmoothLev k r 0 D J) (hL : LeftEq k r z 0 D J) (hR : RightEq k r z' 0 D J)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hW : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g ∈ D)
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hX : IsActualLevel X L) (Y : ℂ) (Φ : RadSp k r z z' π π')
    (hΦ : ∀ c ∈ OmX r, (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = resG k r (Fin.last r) J c g) :
    ∀ c ∈ OmX r, (((L.Ahatv Y).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (AAvop k r r le_rfl (Y - ((2 * r + k : ℕ) : ℂ) / 2) J) c g := by
  set ℓ : ℂ := Y - ((2 * r + k : ℕ) : ℂ) / 2 with hℓ
  set F : ℕ → (Fin r → ℂ) → (Wq →L[ℂ] Wp) :=
    fun m c => La hD (P.PBG.vK hD J hS) (wCell k r (Fin.last r) c * g) (mq hD ℓ m) with hF
  have hFd : ∀ m, ∀ c ∈ OmX r, DifferentiableAt ℝ (F m) c := fun m c hc =>
    diff_cell ((mq (E := Wq →L[ℂ] Wp) hD ℓ m).1 (P.PBG.vK hD J hS)).2.1 hc hg (hW c hc)
  set G : ℕ → (Fin r → ℂ) → (Wq →L[ℂ] Wp) :=
    fun m c => ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • (((-1 : ℂ) ^ m) • F m c) with hG
  have hpb : ∀ (m : ℕ) (l : Fin r), ∀ c ∈ OmX r, pbOp l (G m) c =
      ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • (((-1 : ℂ) ^ m) • pbOp l (F m) c +
        (Y - ℓ - (l.val : ℂ)) • (((-1 : ℂ) ^ m) • F m c)) := by
    intro m l c hc
    rw [hG]
    beta_reduce
    rw [gauge_bar (fun a => Mdim k r a - 1) (fun c => ((-1 : ℂ) ^ m) • F m c) c hc ((hFd m c hc).const_smul ((-1 : ℂ) ^ m)),
      pbOp_csmul _ l (hFd m c hc)]
    congr 3
    have hl := l.isLt
    rw [hℓ]
    simp only [Mdim, Nat.add_sub_cancel]
    push_cast [Nat.cast_sub hl.le]
    ring
  have key := radial_chain X L hX Y Φ g G
    (fun c hc => by
      rw [hΦ c hc, resG_last]
      simp only [hG, hF, mq_zero, pow_zero, one_smul, La_apply]
      congr 1
      exact (cut_of_mem J ⟨wCell_glev hc hg, hW c hc⟩).symm)
    (fun h c hc => by
      rw [hpb 0 ⟨0, h⟩ c hc]
      have e : F 1 c = (-ℓ) • F 0 c + pbOp ⟨0, h⟩ (F 0) c := by
        have h1 := la_torus hD (P.PBG.vK hD J hS) hg hc (hW c hc) ⟨0, h⟩ 1
        rw [mul_one] at h1
        simp only [hF, mq_zero]
        rw [mq_one hD ℓ h, map_sub, h1, Algebra.algebraMap_eq_smul_one, map_smul, sub_neg_eq_add]
      simp only [hG, e]
      push_cast
      module)
    (fun m h c hc => by
      rw [hpb (m + 1) ⟨m + 1, h⟩ c hc]
      have e : F (m + 2) c = (-ℓ - ((m + 1 : ℕ) : ℂ)) • F (m + 1) c + pbOp ⟨m + 1, h⟩ (F (m + 1)) c -
          (star (c ⟨m + 1, h⟩) / star (c ⟨m, by omega⟩)) • F m c :=
        la_step hD hz hz' hDN hS hL hR hg hc (hW c hc) ℓ m h
      simp only [hG, e, pow_succ]
      module)
  intro c hc
  change ((L.Drb.1 ((L.Avr Y).1 Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = _
  rw [drb_apply X L hX, key c hc, resG_last, aav_cell hD hS hg hc (hW c hc), smul_comm]

end cell

section bessel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBN.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem qminor_jf (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    (a b : Fin r → Fin (2 * r + k + 1)) (u : ℂ) {g : Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    Integrable (fun p => xiP Bs p • qminorOp (EabH (Hpk k r)) a b u (rho Bs p F) g) Bs.μSS ∧
      qminorOp (EabH (Hpk k r)) a b u (JF Bs F) g =
        ∫ p, xiP Bs p • qminorOp (EabH (Hpk k r)) a b u (rho Bs p F) g ∂Bs.μSS := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  set A : ℝ := 12 * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hA
  have hT : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A r := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of k r r A le_rfl
  have hFA : InCC A r F := hn.2.1 A r
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq Bs A r F hT hFA
  have hCk : CkOn (r : ℕ∞) (GV k r) F := hFA.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ r →
      Integrable (fun p => xiP Bs p • Rw v (rho Bs p F) g) Bs.μSS ∧
      Rw v (JF Bs F) g = ∫ p, xiP Bs p • Rw v (rho Bs p F) g ∂Bs.μSS := by
    intro v hvu hvl
    obtain ⟨hI, hE⟩ := hW.2 [] v (by simp) hvu (by simpa using hvl) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP Bs p • rho Bs p (dLR [] (v.map (AdR p)) F) g) =ᵐ[Bs.μSS]
        fun p => xiP Bs p • Rw v (rho Bs p F) g := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have := Formalism.FourierDecayAlt.P.rewrite_rho_action k r Wp Wq Bs r F p hp hCk [] v (by simp) (fun X hX => (hvu X hX).1)
        (by simpa using hvl) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    refine ⟨hI.congr hae, ?_⟩
    rw [← integral_congr_ae hae]
    exact hE
  have hlocJ : Loc (r : ℕ∞) (JF Bs F) g := by
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hW.1 g ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg.2⟩
    exact ⟨U, F', hU, hgU, by exact_mod_cast hc, fun x hx hxG => he x hx (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hxG)⟩
  have hT : ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ts.length = r →
      Integrable (fun p => xiP Bs p • foldT ts (rho Bs p F) g) Bs.μSS ∧
        foldT ts (JF Bs F) g = ∫ p, xiP Bs p • foldT ts (rho Bs p F) g ∂Bs.μSS := by
    intro ts hts
    have hae : (fun p => xiP Bs p • foldT ts (rho Bs p F) g) =ᵐ[Bs.μSS]
        fun p => ((expand k r ts).map fun cw => cw.1 • (xiP Bs p • Rw cw.2 (rho Bs p F) g)).sum := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      rw [expand_eq ts _ g hgG (loc_rho Bs hn.1 hp hgG _), smul_list_sum]
      congr 1
      refine List.map_congr_left fun cw _ => ?_
      exact smul_comm _ _ _
    have := int_list (μ := Bs.μSS) (expand k r ts)
      (fun cw p => xiP Bs p • Rw cw.2 (rho Bs p F) g) (fun cw => Rw cw.2 (JF Bs F) g) (fun cw hcw => by
        have hw := expand_words ts cw hcw
        rw [hts] at hw
        exact key cw.2 hw.1 hw.2)
    refine ⟨this.1.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, this.2, expand_eq ts _ g hgG (by rw [hts]; exact hlocJ)]
  have hT' := fun σ : Equiv.Perm (Fin r) => hT
    (List.ofFn fun j : Fin r => (u - ((j : ℕ) : ℂ), a (σ j), b j)) (by simp)
  have e : ∀ p, xiP Bs p • qminorOp (EabH (Hpk k r)) a b u (rho Bs p F) g =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (xiP Bs p •
        foldT (List.ofFn fun j : Fin r => (u - ((j : ℕ) : ℂ), a (σ j), b j)) (rho Bs p F) g) := by
    intro p
    rw [Formalism.FourierDecayAlt.P.PBG.qminor_foldT, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact integrable_finsetSum _ fun σ _ => Formalism.FourierDecayAlt.P.PBG.integrable_csmul _ (hT' σ).1
  · simp only [e]
    rw [integral_finsetSum _ fun σ _ => Formalism.FourierDecayAlt.P.PBG.integrable_csmul _ (hT' σ).1, Formalism.FourierDecayAlt.P.PBG.qminor_foldT]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_smul, (hT' σ).2]

theorem jf_aav (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (ell : ℂ)
    {g : Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    JF Bs (C3.AAvop k r r le_rfl ell F) g = C3.AAvop k r r le_rfl ell (JF Bs F) g := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  show ∫ p, xiP Bs p • rho Bs p (C3.AAvop k r r le_rfl ell F) g ∂Bs.μSS = _
  have hae : ∀ᵐ p ∂Bs.μSS, xiP Bs p • rho Bs p (C3.AAvop k r r le_rfl ell F) g =
      ∑ B : Fin r → Fin (2 * r + k + 1), (if StrictMono (fun l => C3.keyS k r (B l)) then
        (Matrix.of fun a l : Fin r => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det •
          (xiP Bs p • qminorOp (EabH (Hpk k r)) B (C3.sR k r r le_rfl) (ell + (r : ℂ) - 1) (rho Bs p F) g)
        else 0) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
    rw [(Formalism.FourierDecayAlt.P.PBG.rho_AA Bs hn.1 r le_rfl 0 ell hp hg.1).2]
    simp only [C3.AAvop, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [smul_comm]
    · simp
  rw [integral_congr_ae hae, integral_finsetSum]
  · simp only [C3.AAvop]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [integral_smul, ← (qminor_jf Bs hF c _ _ hg).2]
    · simp
  · intro c _
    split_ifs
    · exact Formalism.FourierDecayAlt.P.PBG.integrable_csmul _ (qminor_jf Bs hF c _ _ hg).1
    · exact integrable_zero _ _ _

end bessel

section main

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

open scoped Classical in

def coefV (k r : ℕ) (Bi : Fin r → Fin (2 * r + k + 1)) (g : B.Mat k r) : ℂ :=
  if StrictMono (fun l => C3.keyS k r (Bi l)) then
    (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (Bi l)).det
  else 0

theorem coefV_poly (k r : ℕ) (Bi : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (coefV k r Bi) := by
  unfold coefV
  split_ifs
  · refine Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_det _ fun a l => ?_
    have e : (fun g : B.Mat k r => (Matrix.of fun a l : Fin r =>
        ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (Bi l)) a l) =
        fun g => ∑ q, ∑ p, (Hpk k r (Bi l) p * Hpk k r q (eI k r a)) * star (g q p) := by
      funext g
      simp only [Matrix.of_apply, bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.sum_mul, Fin.castLE_rfl, id]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [e]
    refine Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sum _ fun q _ => Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sum _ fun p _ => ?_
    exact Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const _ 0) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_star_entry q p)
  · exact Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 _

theorem polyLift_ahatv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahatv y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ hNF y
  set ℓ : ℂ := (y : ℂ) - ((2 * P.r + P.k : ℕ) : ℂ) / 2 with hℓ
  obtain ⟨Θ, hΘ, hap⟩ := GlobalTheory.HatNF.MinorPoly.minor_polyOp Wp Wq P.k P.r P.r P.r (Fin P.r → Fin (2 * P.r + P.k + 1)) (fun Bi => Bi)
    (fun _ => C3.sR P.k P.r P.r le_rfl) (ℓ + (P.r : ℂ) - 1) (coefV P.k P.r) (coefV_poly P.k P.r)
  refine ⟨Θ, fun T hT => ?_, fun F hF Φ hΦ x hx => ?_⟩
  · obtain ⟨h1, Pp, h2, h3⟩ := hΘ T hT
    exact ⟨by omega, Pp, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mono (by nlinarith) h2, h3⟩
  · have hG : ∀ g ∈ B.GV P.k P.r, B.opApply Θ F g = (1 : ℂ) • C3.AAvop P.k P.r P.r le_rfl ℓ F g := by
      intro g hg
      rw [hap F g hg Set.univ isOpen_univ trivial (by rw [Set.inter_univ]; exact hF.1), one_smul]
      unfold C3.AAvop coefV
      rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg]
      refine Finset.sum_congr rfl fun Bi _ => ?_
      split_ifs
      · rfl
      · rw [zero_smul]
    have hOm := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx
    obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
    obtain ⟨hS, hL, hR, -⟩ := Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := P.k) (r := P.r) Bs.z_mem Bs.z'_mem
    have h1S : ∀ w : Fin (2 * P.r + P.k + 1) → ℂ, ∀ n ∈ Q.Nlev P.k P.r 0, n ∈ Q.Slev P.k P.r w 0 :=
      fun w n hn => ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw w, n, hn, (Matrix.one_mul n).symm⟩
    have key := cell_radial hDom.1 Bs.z_mem Bs.z'_mem
      (fun g hg n hn => by
        have := hDom.2 g hg n (h1S _ n hn) 1
          (h1S _ 1 ⟨(Formalism.QuantumDeterminants.nSubgroup P.k P.r).1, Formalism.FourierDecayAlt.P.Qx3.glev_one _⟩)
        rwa [Matrix.mul_one] at this)
      hS hL hR hx.2.1 (fun c hc => (Formalism.FourierDecayAlt.P.TLB.wCell_om Bs (x := (c, x.2)) ⟨hc, hx.2⟩).2)
      X d.L hNF.1 (y : ℂ) Φ (fun c hc => hΦ (c, x.2) ⟨hc, hx.2⟩) x.1 hx.1
    rw [key]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs hG hOm.1, one_smul, jf_aav Bs hF ℓ hOm]

end main

end GlobalTheory.MirrorToda
