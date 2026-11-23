import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PeriodBound

theorem period_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb
  obtain ⟨C0, hC0⟩ := hFb
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV V v.μ v.𝓕 v.haar v.fund
  have hval : ∀ x : SmT M, Continuous (t x) ∧ ∃ B : ℝ, ∀ g, ‖t x g‖ ≤ B := by
    intro x
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ t ht x
    exact ⟨ha.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ha hc⟩
  have hint0 : ∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ := by
    intro x
    obtain ⟨hcont, B, hB⟩ := hval x
    refine Measure.integrableOn_of_bounded (M := C0 * B) hfin.ne
      ((hF.2.mul hcont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul (hC0 g) (hB g) (norm_nonneg _) ((norm_nonneg _).trans (hC0 g))
  refine ⟨hint0, ?_⟩
  set T : MMap M := PiTensorProduct.lift.symm t with hTdef
  have hT : T ∈ Mult θ M J χ := (mem_multT θ M J χ t).1 ht
  obtain ⟨c, hc⟩ := GlobalTheory.SchurConst.schurMult_all hP D θ hθ V S M J χ v.μ v.𝓕 v.haar v.fund hθ v.haar v.fund T hT T hT
  have hTw : ∀ w : M.Vec, T w = t (PiTensorProduct.tprod ℂ w) := fun w => by
    rw [hTdef, PiTensorProduct.lift_symm]
    rfl
  set C' : ℝ := max C0 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hFC : ∀ g, ‖F g‖ ≤ C' := fun g => (hC0 g).trans (le_max_left _ _)
  refine ⟨C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2, fun w => ?_⟩
  set s : ℝ := ∏ τ, ‖(w τ : M.H τ)‖ with hs
  have hs0 : 0 ≤ s := Finset.prod_nonneg fun τ _ => norm_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h0.symm
    have hwτ : w τ = 0 := Subtype.ext (norm_eq_zero.1 hτ)
    have h1 : PiTensorProduct.tprod ℂ w = 0 := (PiTensorProduct.tprod ℂ).map_coord_zero τ hwτ
    rw [h1, map_zero, ← h0]
    simp
  · obtain ⟨hint, heq⟩ := hc w w
    have hnsq : ∀ g, ‖star (T w g) * T w g‖ = ‖T w g‖ ^ 2 := fun g => by
      rw [norm_mul, norm_star, sq]
    have hint2 : IntegrableOn (fun g => ‖T w g‖ ^ 2) v.𝓕 v.μ := by
      have h := funext fun g => (hnsq g).symm
      rw [h]
      exact hint.norm
    have hsq : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ ≤ ‖c‖ * s ^ 2 := by
      have h1 : ((∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ : ℝ) : ℂ) = ∫ g in v.𝓕, star (T w g) * T w g ∂v.μ := by
        rw [← integral_complex_ofReal]
        congr 1
        funext g
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
      have hnn : 0 ≤ ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := integral_nonneg fun g => sq_nonneg _
      have h2 : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ = ‖∫ g in v.𝓕, star (T w g) * T w g ∂v.μ‖ := by
        rw [← h1, Complex.norm_of_nonneg hnn]
      rw [h2, heq, norm_mul, norm_prod, hs, ← Finset.prod_pow]
      refine le_of_eq ?_
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hpt : ∀ g, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ≤ C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by
      intro g
      rw [norm_mul, ← hTw]
      have h3 : ‖T w g‖ ≤ s / 2 + ‖T w g‖ ^ 2 / (2 * s) := by
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖T w g‖ - s)]
      calc ‖F g‖ * ‖T w g‖ ≤ C' * ‖T w g‖ := mul_le_mul_of_nonneg_right (hFC g) (norm_nonneg _)
        _ ≤ C' * (s / 2 + ‖T w g‖ ^ 2 / (2 * s)) := mul_le_mul_of_nonneg_left h3 hC'0
        _ = C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by ring
    have hintR : IntegrableOn (fun g => C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) v.𝓕 v.μ :=
      (integrableOn_const hfin.ne).add (hint2.const_mul _)
    calc ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖
        ≤ ∫ g in v.𝓕, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ∂v.μ := norm_integral_le_integral_norm _
      _ ≤ ∫ g in v.𝓕, (C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) ∂v.μ :=
          integral_mono (hint0 _).norm hintR hpt
      _ = (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := by
          have hc1 : Integrable (fun _ : GA D V => C' * s / 2) (v.μ.restrict v.𝓕) := integrableOn_const hfin.ne
          have hc2 : Integrable (fun g => C' / (2 * s) * ‖T w g‖ ^ 2) (v.μ.restrict v.𝓕) := hint2.const_mul _
          rw [integral_add hc1 hc2, setIntegral_const,
            integral_const_mul, smul_eq_mul, Measure.real]
      _ ≤ (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * (‖c‖ * s ^ 2) := by
          gcongr
      _ = C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2 * s := by
          field_simp

end GlobalTheory.PeriodBound
