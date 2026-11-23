import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagTens

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

theorem finprod_indicator {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ w : Pl F, Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))) =
    (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}).indicator
      (fun _ => (1 : ℂ)) y := by
  by_cases h : ∀ i (w : Pl F), y i w ∈ w.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}) from Set.mem_univ_pi.2 fun i => h i)]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
      {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from fun i => h i w)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl F, x w ∈ w.adicCompletionIntegers F}) from fun hy => h fun i => Set.mem_univ_pi.1 hy i)]
    push_neg at h
    obtain ⟨i₀, w₀, hw₀⟩ := h
    have hfin : (Function.mulSupport fun w : Pl F => Set.indicator
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
        (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))).Finite := by
      have hx : ∀ᶠ w in Filter.cofinite, ∀ i, (y i) w ∈ w.adicCompletionIntegers F := by
        rw [Filter.eventually_all]
        intro i
        exact (y i).2
      refine Set.Finite.subset (Filter.eventually_cofinite.1 hx) ?_
      intro w hw hw'
      apply hw
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from hw')]
      rfl
    refine finprod_eq_zero _ w₀ ?_ hfin
    exact Set.indicator_of_notMem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w₀ (y i)) ∉
      {x : κ → Fv F w₀ | ∀ i, x i ∈ w₀.adicCompletionIntegers F} from fun hy => hw₀ (hy i₀)) _

theorem lDiag_box_tens_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F), ∃ φ₀ ∈ SB (κ → Fv F v), boxFun φ₀ φ₀ ∈ SB (κ ⊕ κ → Fv F v) ∧
    ∃ R R' : (κ → AF F) → ℂ, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R ∧ Rest (evFin F v) φ R') ∧
      GlobalTheory.DiagForm.lDiag F κ (boxFun (tens (evFin F v) φ₀ R) (tens (evFin F v) φ₀ R')) ≠ 0 := by
  intro F _ _ κ _ v
  classical
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), x w ∈ w.adicCompletionIntegers F} with hOdef
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SInf F κ := hc.toSchwartzMap hd
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let φs : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r := fun φ hφ => ⟨hr, by
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w⟩
  have h0 : φs v ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨φs v, h0, ?_, r, r, fun φ hφ => ⟨hRest φ hφ, hRest φ hφ⟩, ?_⟩
  · have e : boxFun (φs v) (φs v) = Set.indicator {x : κ ⊕ κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      funext x
      simp only [boxFun, φs, Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, Sum.forall, Pi.one_apply]
      split_ifs <;> simp_all
    rw [e]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  · set V : Set (GlobalTheory.DiagForm.Vf F κ) := Set.univ.pi fun _ => O with hVdef
    set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := V.indicator fun _ => (1 : ℂ) with hgdef
    have hΦ : tens (evFin F v) (φs v) r = pureA F f g := by
      rw [hrt, Function.update_eq_self]
      funext x
      show f _ * _ = f _ * _
      congr 1
      exact finprod_indicator _
    have hΦs : tens (evFin F v) (φs v) r ∈ schA F κ := (hRest _ h0).2
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hΦs _ hΦs
    have hint := GlobalTheory.DiagForm.integrable_resD hbox
    have hres : GlobalTheory.DiagForm.resD F κ (boxFun (tens (evFin F v) (φs v) r) (tens (evFin F v) (φs v) r)) =
        fun p => ((b (GlobalTheory.DiagForm.eI F κ p.1) * b (GlobalTheory.DiagForm.eI F κ p.1) : ℝ) : ℂ) * (g p.2 * g p.2) := by
      rw [hΦ]
      funext p
      show pureA F f g _ * pureA F f g _ = _
      have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((GlobalTheory.DiagForm.glue p) i).1) =
          GlobalTheory.DiagForm.eI F κ p.1 := by
        funext i; simp [GlobalTheory.DiagForm.glue]
      have e2 : (fun i => ((GlobalTheory.DiagForm.glue p) i).2) = p.2 := rfl
      simp only [pureA, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
      rw [e1, e2, hf]
      push_cast
      ring
    rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, GlobalTheory.DiagForm.Lext_apply _ hint, hres, GlobalTheory.DiagForm.mu,
      integral_prod_mul (fun u => ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ))
        (fun y => g y * g y)]
    have h0O : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun w => (w.adicCompletionIntegers F).zero_mem
    have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
    have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
    have hgg : (fun y => g y * g y) = V.indicator fun _ => (1 : ℂ) := by
      funext y
      simp only [hgdef, Set.indicator_apply]
      split_ifs <;> simp
    have hc2 : (∫ y, g y * g y ∂(Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ))) ≠ 0 := by
      rw [hgg, integral_indicator_const _ hVo.measurableSet]
      have hpos : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0O⟩
      have hfin : (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V < ⊤ := hVc.measure_lt_top
      have : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
      simpa using this.ne'
    have hc1 : (∫ u, ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ)
        ∂(volume : Measure (GlobalTheory.DiagForm.Vi F κ))) ≠ 0 := by
      rw [integral_complex_ofReal]
      have hcs1 : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.eI F κ u) :=
        b.hasCompactSupport.comp_homeomorph (GlobalTheory.DiagForm.eI F κ).toHomeomorph
      have hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) := hcs1.mul_right
      have hcont : Continuous fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) :=
        (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous).mul (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous)
      have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => mul_nonneg b.nonneg b.nonneg) (by
          simp only [map_zero]
          rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
          norm_num)
      exact_mod_cast hpos.ne'
    exact mul_ne_zero hc1 hc2

end GlobalTheory.DiagTens
