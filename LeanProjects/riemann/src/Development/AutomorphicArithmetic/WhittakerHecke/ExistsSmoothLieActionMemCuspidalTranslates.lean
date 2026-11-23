import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem rt_infGL_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) =
      lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z))
    (Units.inv_mul_cancel_right (y.val * X) y).symm

private theorem lie_rt_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (A E)) :
    ∃ Y : Lie E a, lie E a (toL X) * rt E a h = rt E a h * lie E a Y := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) h with hy
  set κ := Matrix.GeneralLinearGroup.map (pFin E) h with hκ
  have hh : h = infGL E a y * finGL E a κ := (infGL_mul_finGL h).symm
  refine ⟨toL ((y⁻¹).val * X * y.val), ?_⟩
  have e : y.val * ((y⁻¹).val * X * y.val) * (y⁻¹).val = X := by
    simp [Matrix.mul_assoc]
  have key := rt_infGL_lie y ((y⁻¹).val * X * y.val)
  rw [e] at key
  conv_lhs => rw [hh, map_mul, ← mul_assoc, ← key, mul_assoc, lie_rt_fin, ← mul_assoc]
  rw [← map_mul, ← hh]

theorem UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (X : Lie E 2) (φ : GL (Fin 2) (A E) → ℂ), φ ∈ Tr P → ∃ f : Sm E 2, f.1 = φ ∧ (lie E 2 X f).1 ∈ Tr P := by
  intro E _ _ _ P X φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, hf, h, rfl⟩ := hφ
    obtain ⟨Y, hY⟩ := lie_rt_eq (a := 2) (E := E) X h
    refine ⟨rt E 2 h ⟨f.1, f.2⟩, rfl, ?_⟩
    have e : lie E 2 X (rt E 2 h f) = rt E 2 h (lie E 2 Y f) := LinearMap.congr_fun hY f
    have hm : lie E 2 Y f ∈ P.V := P.stable (.lie Y) f hf
    refine Submodule.subset_span ⟨_, hm, h, ?_⟩
    rw [show (⟨f.1, f.2⟩ : Sm E 2) = f from rfl, e]
    rfl
  | zero => exact ⟨0, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨fa, rfl, ha⟩ := ha
    obtain ⟨fb, rfl, hb⟩ := hb
    refine ⟨fa + fb, rfl, ?_⟩
    rw [map_add]
    exact (Tr P).add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨fa, rfl, ha⟩ := ha
    refine ⟨c • fa, rfl, ?_⟩
    rw [map_smul]
    exact (Tr P).smul_mem c ha
