import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpanStatement

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_add (F G : GA E a → ℂ) (g : GA E a) : chart (F + G) g = chart F g + chart G g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_smul (z : ℂ) (F : GA E a → ℂ) (g : GA E a) : chart (z • F) g = z • chart F g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_zero (g : GA E a) : chart (0 : GA E a → ℂ) g = 0 := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem kSpan_diff : ∀ F ∈ kSpan E a, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    obtain ⟨L, hL, -⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g u
    exact hL.differentiableAt.differentiableWithinAt
  | zero => intro g; rw [chart_zero]; exact differentiableOn_const 0
  | add F G _ _ hF hG => intro g; rw [chart_add]; exact (hF g).add (hG g)
  | smul z F _ hF => intro g; rw [chart_smul]; exact (hF g).const_smul z

theorem differentiableAt_one_of_mem {F : GA E a → ℂ} (hF : F ∈ kSpan E a) (g : GA E a) :
    DifferentiableAt ℝ (chart F g) (oneL E a) :=
  (kSpan_diff F hF g).differentiableAt (isOpen_invSet.mem_nhds isUnit_one)

theorem kSpan_lie : ∀ F ∈ kSpan E a, ∀ Y : Lie E a, lieD Y F ∈ kSpan E a := by
  intro F hF Y
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    have e : lieD Y (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) = fun g : GA E a =>
        ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν := by
      funext g
      obtain ⟨L, hL, hZ⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g 1
      have e1 : toL (1 : GL (Fin a) (Cinf E)).val = oneL E a := rfl
      rw [lieD, ← e1, hL.fderiv, hZ Y]
      simp
    rw [e]
    exact GlobalTheory.T.rapidKernel_integral_conjLieDerivative_mem_span E a G X ν k γ Y hk hG
  | zero =>
    have e : lieD Y (0 : GA E a → ℂ) = 0 := by
      funext g; simp [lieD, chart_zero]
    rw [e]; exact zero_mem _
  | add F G hF' hG' hF hG =>
    have e : lieD Y (F + G) = lieD Y F + lieD Y G := by
      funext g
      simp only [lieD, chart_add, Pi.add_apply]
      rw [fderiv_add (differentiableAt_one_of_mem hF' g) (differentiableAt_one_of_mem hG' g)]
      rfl
    rw [e]; exact add_mem hF hG
  | smul z F hF' hF =>
    have e : lieD Y (z • F) = z • lieD Y F := by
      funext g
      simp only [lieD, chart_smul, Pi.smul_apply]
      rw [fderiv_const_smul (differentiableAt_one_of_mem hF' g)]
      rfl
    rw [e]; exact Submodule.smul_mem _ z hF

theorem kSpan_le_Sm : kSpan E a ≤ Sm E a := GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable E a _ kSpan_diff kSpan_lie

theorem kSpan_decays_growth : ∀ F ∈ kSpan E a, GlobalTheory.ShortVecDecay.Decays F ∧ Growth F := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    exact ⟨GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator E a G X ν k γ hk hG.decays, GlobalTheory.T.moderateGrowth_rapidKernelOperator E a G X ν k γ hk hG.growth⟩
  | zero => exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩
  | add F G _ _ hF hG => exact ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  | smul z F _ hF => exact ⟨hF.1.smul z, hF.2.smul z⟩

theorem word_mem_kSpan (l : List (Lie E a)) (φ : Sm E a) (hφ : φ.1 ∈ kSpan E a) :
    (GlobalTheory.GLFin.word l φ).1 ∈ kSpan E a := by
  induction l with
  | nil => simpa [GlobalTheory.GLFin.word] using hφ
  | cons Y l ih => rw [word_cons]; exact kSpan_lie _ ih Y

theorem Good.kernel {G : GA E a → ℂ} (hG : Good G) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    Good (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) := by
  have hm : (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) ∈ kSpan E a :=
    Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, k, γ, G, hk, hG, rfl⟩
  exact ⟨kSpan_le_Sm hm, fun l => kSpan_decays_growth _ (word_mem_kSpan l _ hm)⟩

variable (E a) in

def goodSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Good F}
  add_mem' := Good.add
  zero_mem' := good_zero
  smul_mem' c _ h := h.smul c

theorem mspanR_le_goodSub {π : CuspSub E a} (hπ : π.IsUnitary) : GlobalTheory.JSW.mspanR π ≤ goodSub E a :=
  sInf_le ⟨fun φ hφ => good_of_mem hπ hφ, fun F hF h => GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate E a F h hF,
    fun F hF X _ ν _ k γ hk => Good.kernel (G := F) hF hk⟩

theorem norm_le_of_short_vector_mspanR : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  intro E _ _ _ a π hπ φ hφ l
  have hg : Good φ.1 := hφ.elim (good_of_mem hπ) fun h => mspanR_le_goodSub hπ h
  obtain ⟨h, hl⟩ := hg
  exact (hl l).1

end GlobalTheory.MSpanDecay
