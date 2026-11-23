import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Mathlib.Analysis.Complex.Conformal

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf UpperTheory.V.Sd Topology
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br.DescentHolomorphic

open Classical in

private def EE (i j : Fin 2) : TR.Lie ℚ 2 := TR.toL (Matrix.single i j (Pi.single Rat.infinitePlace 1))

private def AA (w : ℂ) : TR.Lie ℚ 2 := w.im • EE 0 0 + w.re • EE 0 1 + EE 1 1

private theorem AA_eq (w : ℂ) (h : w.im ≠ 0) :
    AA w = TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 w.im h) w.re)).val := by
  funext i j v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change _ = (aff (Units.mk0 w.im h) w.re).val i j
  fin_cases i <;> fin_cases j <;> simp [AA, EE, aff, Matrix.single]

private theorem rmul_AA (w : ℂ) (j : Fin 2) : TR.rmul (EE 0 j) (AA w) = w.im • EE 0 j := by
  funext a b v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change (Matrix.of (AA w) * Matrix.of (EE 0 j)) a b Rat.infinitePlace = _
  fin_cases a <;> fin_cases b <;> fin_cases j <;> simp [AA, EE, Matrix.single, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem chart_AA (ψ : GA ℚ 2 → ℂ) (w : ℂ) (h : w.im ≠ 0) :
    TR.chart ψ 1 (AA w) = ψ (upR (aff (Units.mk0 w.im h) w.re)) := by
  rw [AA_eq w h, TR.chart_val, one_mul]
  rfl

private theorem hasFDerivAt_AA (w : ℂ) :
    HasFDerivAt AA (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)) w :=
  (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)).hasFDerivAt.add_const (EE 1 1)

private theorem key (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (w : ℂ) (hw : 0 < w.im) :
    DifferentiableAt ℂ (fun w : ℂ => ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * TR.chart φ.1 1 (AA w)) w := by
  have hm : AA w ∈ TR.invSet ℚ 2 := by rw [AA_eq w hw.ne']; exact TR.val_mem_invSet _
  have hc := ((TR.contDiffAt_chart φ.2 1 hm).differentiableAt (by simp)).hasFDerivAt
  set D := fderiv ℝ (TR.chart φ.1 1) (AA w) with hD
  set g := upR (aff (Units.mk0 w.im hw.ne') w.re) with hg
  have he : ∀ j, (TR.Eop Rat.infinitePlace 0 j φ).1 g = (w.im : ℂ) * D (EE 0 j) := fun j => by
    have h1 := TR.chart_lieD φ.2 (EE 0 j) 1 hm
    rw [chart_AA _ w hw.ne', rmul_AA, map_smul, Complex.real_smul] at h1
    exact h1
  have h1 : (TR.Eop Rat.infinitePlace 0 1 φ).1 g - (TR.Eop Rat.infinitePlace 1 0 φ).1 g = Complex.I * k * φ.1 g :=
    congrFun (congrArg Subtype.val (hφ.wt Rat.infinitePlace)) g
  have h2 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g - (TR.Eop Rat.infinitePlace 1 1 φ).1 g =
      Complex.I * ((TR.Eop Rat.infinitePlace 0 1 φ).1 g + (TR.Eop Rat.infinitePlace 1 0 φ).1 g) :=
    congrFun (congrArg Subtype.val (hφ.low Rat.infinitePlace)) g
  have h3 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g + (TR.Eop Rat.infinitePlace 1 1 φ).1 g = 0 :=
    congrFun (congrArg Subtype.val (hφ.one Rat.infinitePlace)) g
  rw [he] at h1 h2 h3
  rw [he] at h2
  have h4 : (w.im : ℂ) * D (EE 0 0) = Complex.I * (w.im * D (EE 0 1)) + k / 2 * φ.1 g := by
    linear_combination (h2 + h3) / 2 - Complex.I / 2 * h1 - (k / 2 * φ.1 g) * Complex.I_mul_I
  have hp := Complex.ofRealCLM.hasFDerivAt.comp w
    ((Complex.imCLM.hasFDerivAt (x := w)).rpow_const (p := -((k : ℝ) / 2)) (Or.inl hw.ne'))
  have hF := hp.fun_mul (hc.comp w (hasFDerivAt_AA w))
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨hF.differentiableAt, ?_⟩
  erw [hF.fderiv]
  have hy : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hr : w.im ^ (-((k : ℝ) / 2) - 1) = w.im ^ (-((k : ℝ) / 2)) / w.im := Real.rpow_sub_one hw.ne' _
  simp [chart_AA _ w hw.ne', ← hg, hr]
  field_simp
  linear_combination 2 * ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * h4

end UpperTheory.V.Br.DescentHolomorphic

open UpperTheory.V.Br.DescentHolomorphic in
theorem UpperTheory.V.Br.downHol :
    UpperTheory.V.Br.DownHol := by
  intro k φ hφ
  refine UpperHalfPlane.mdifferentiable_iff.2 ?_
  refine DifferentiableOn.congr (fun w hw => (key k φ hφ w hw).differentiableWithinAt) fun w hw => ?_
  have hw' : 0 < w.im := hw
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hw', chart_AA _ w hw'.ne']
  rfl
