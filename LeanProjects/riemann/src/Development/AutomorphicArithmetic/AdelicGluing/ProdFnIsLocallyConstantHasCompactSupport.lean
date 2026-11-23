import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

private theorem one_apply_pi (i j : Fin n) (w : PlacesOver E v) :
    (1 : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i j w =
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij]

private noncomputable def glGlue (x : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E)) :
    GL (Fin n) (CompletionsOver E v) where
  val := Matrix.of fun i j w => (x w).val i j
  inv := Matrix.of fun i j w => ((x w)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).val_inv i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1
  inv_val := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).inv_val i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1

private theorem glGlue_continuous :
    Continuous (glGlue (E := E) (n := n) (v := v)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply w)
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_inv.comp (continuous_apply w))

private theorem glGlue_cmp (g : GL (Fin n) (CompletionsOver E v)) :
    glGlue (fun w => UpperTheory.ConvolutionTheory.GM.cmp w g) = g := by
  ext i j w
  rfl

end

theorem UpperTheory.prodFn_isLocallyConstant_hasCompactSupport :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ),
        (∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) →
        IsLocallyConstant (prodFn h) ∧ HasCompactSupport (prodFn h) := by
  intro F E _ _ _ _ _ n v h hh
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  have hp : prodFn h = fun g => ∏ w, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
    funext g
    exact finprod_eq_prod_of_fintype _
  constructor
  · have key : ∀ s : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ s, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hh a).1.comp_continuous (cmp_continuous a)).mul ih
    rw [hp]
    exact key Finset.univ
  · have hK : IsCompact (glGlue '' Set.pi Set.univ fun w : PlacesOver E v => tsupport (h w)) :=
      (isCompact_univ_pi fun w => (hh w).2).image glGlue_continuous
    refine HasCompactSupport.of_support_subset_isCompact hK fun g hg => ?_
    refine ⟨fun w => UpperTheory.ConvolutionTheory.GM.cmp w g, fun w _ => subset_tsupport _ ?_, glGlue_cmp g⟩
    rw [Function.mem_support, hp] at hg
    intro h0
    exact hg (Finset.prod_eq_zero (Finset.mem_univ w) h0)
