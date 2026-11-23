import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem isClosed_valuation_le (w : HeightOneSpectrum (𝓞 F)) (γ : WithZero (Multiplicative ℤ)) :
    IsClosed {x : w.adicCompletion F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < Valued.v x := lt_of_not_ge hx
  filter_upwards [Valued.locally_const (lt_of_le_of_lt zero_le hx').ne'] with y hy
  intro hy'
  have e : Valued.v y = Valued.v x := hy
  exact absurd (e ▸ hy') (not_le.mpr hx')

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 F)) : Continuous (pLoc F w) :=
  RestrictedProduct.continuous_eval w

theorem continuous_pFin : Continuous (pFin F) := continuous_snd

theorem continuous_pInf : Continuous (UpperTheory.V.TR.pInf F) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem isClosed_row (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      (((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1))).sub continuous_const)

theorem isClosed_col (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1)))

theorem coe_scalar (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.diagonal fun _ => (a : Ad F) := rfl

theorem continuous_av : Continuous (av (F := F)) :=
  ((continuous_moduleSection (w0 F)).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_rowv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => rowv g a ξ := by
  unfold rowv Mrow
  simp only [Units.val_mul, coe_scalar]
  exact continuous_const.matrix_vecMul
    ((continuous_pi fun _ => Units.continuous_val).matrix_diagonal.matrix_mul continuous_const)

theorem continuous_colv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => colv g a ξ := by
  unfold colv Mcol
  simp only [Units.val_mul, coe_scalar]
  exact (continuous_const.matrix_mul
    (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal).matrix_mulVec continuous_const

theorem continuous_vInf : Continuous (vInf (F := F)) :=
  continuous_pi fun i => continuous_pInf.comp (continuous_apply i)

theorem measurable_finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finRow c (f p) := by
  unfold finRow
  exact Measurable.ite ((isClosed_row c).preimage hf).measurableSet measurable_const measurable_const

theorem measurable_finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finCol c (f p) := by
  unfold finCol
  refine Measurable.ite ((isClosed_col c).preimage hf).measurableSet ?_ measurable_const
  exact (continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_pFin.comp ((continuous_apply 1).comp hf)))).measurable

theorem measurable_chi (χ : HChar F) : Measurable fun p : Pp F => ((χ.1 (av p) : ℂˣ) : ℂ)⁻¹ :=
  ((Units.continuous_val.comp (χ.2.1.comp continuous_av)).measurable).inv

theorem measurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap1 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finRow c ((continuous_rowv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable

theorem measurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap2 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finCol c ((continuous_colv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable.inv

theorem measurable_row_weight (g : GA F 2) : Measurable (w1 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_rowv g ξ.1).comp continuous_av)).measurable

theorem measurable_column_weight (g : GA F 2) : Measurable (w2 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_colv g ξ.1).comp continuous_av)).measurable

theorem aestronglyMeasurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap1 χ c g) (μS F S) := (measurable_first_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap2 χ c g) (μS F S) := (measurable_second_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_row_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w1 g) (μS F S) :=
  (measurable_row_weight g).aestronglyMeasurable

theorem aestronglyMeasurable_column_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w2 g) (μS F S) :=
  (measurable_column_weight g).aestronglyMeasurable

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
