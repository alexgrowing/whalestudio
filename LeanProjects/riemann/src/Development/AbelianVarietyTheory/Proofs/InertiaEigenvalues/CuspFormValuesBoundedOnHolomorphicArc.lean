import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrameStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArcBdd

theorem norm_prod_pow_le {ι : Type} [Fintype ι] (f : ι → ℂ) (e : ι → ℕ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∏ i, f i ^ e i‖ ≤ B ^ (∑ i, e i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hf i) _

theorem pnorm_unitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (hx : GlobalTheory.FrameNorm.IsUnitFr X x) :
    X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, hx τ i.succ, hx τ i.castSucc, div_one]
  simp only [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem holSub_bdd {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : (k : Comp) → Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X)
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) :
    ∃ C : ℝ, ∀ x ∈ (X k).dom, (X k).pnorm (la k) (P k) x ≤ C := by
  unfold Formalism.L2.PjFree.holSub at hP
  induction hP using Submodule.span_induction with
  | mem P hP => exact (hP k).1.2
  | zero => exact ⟨0, fun x _ => by
      have := Formalism.L2.Pj.pnorm_zero (X k) (la k) x
      simpa using this.le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨C1, h1⟩ := hP
    obtain ⟨C2, h2⟩ := hQ
    exact ⟨C1 + C2, fun x hx => (Formalism.L2.Pj.pnorm_add_le (X k) (la k) (P k) (Q k) x).trans (add_le_add (h1 x hx) (h2 x hx))⟩
  | smul s P _ hP =>
    obtain ⟨C1, h1⟩ := hP
    exact ⟨‖s‖ * C1, fun x hx => by
      have := Formalism.L2.Pj.pnorm_smul (X k) (la k) s (P k) x
      simp only [Pi.smul_apply] at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1 x hx) (norm_nonneg _)⟩

theorem cusp_bounded_at_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Formalism.L2.PjFree.GoodEmb c σ → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ M : ℝ, ∀ (k : (U σ).Comp) (x : ((U σ).X k).dom), GlobalTheory.FrameNorm.IsUnitFr ((U σ).X k) x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x))‖ ≤ M := by
  intro E _ _ _ H Dw l Xo c r U σ a' n F hG hF
  haveI := (U σ).fin
  have hF' : Formalism.L2.PjFree.rdU (U σ) F ∈ Formalism.L2.PjFree.holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) := by
    unfold Formalism.L2.PjFree.cusp at hF
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hF
    have := hF.2 σ
    rw [Submodule.mem_iInf] at this
    exact Submodule.mem_comap.mp (this hG)
  choose C hC using holSub_bdd (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) _ hF'
  refine ⟨∑ k, max (C k) 0, fun k x hx => ?_⟩
  have h1 := hC k x.1 x.2
  rw [pnorm_unitFr _ _ _ _ hx] at h1
  have h2 : Formalism.L2.PjFree.rdU (U σ) F k x.1 = Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) := by
    simp [Formalism.L2.PjFree.rdU, x.2]
  rw [← h2]
  refine h1.trans ((le_max_left (C k) 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (C k) 0) (fun k _ => le_max_right _ _) (Finset.mem_univ k)

theorem cusp_values_bounded_on_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c r U σ Uw _ _ O _ β Y a χ W Ha th Θ z hU hG hz a' n F hD hF
  obtain ⟨T1, B1, h1⟩ := GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨T2, B2, h2⟩ := GlobalTheory.T.arc_generator_ratio_bounded_unit_frame E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨M, hM⟩ := cusp_bounded_at_unitFr E H Dw l Xo c r U σ a' n F hG hF
  have hev := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  set B := max 1 (max B1 B2)
  refine ⟨max T1 T2, max M 0 * B ^ (∑ i, ex Dw a' n i), ?_⟩
  intro w hw yw hyw
  obtain ⟨k, x, t, hux, hb⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hG (hU σ hG)).2 yw
  have hsc := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a' n F (Formalism.L2.PjFree.cusp_le_sec Xo c U a' n hF) (CAt σ)).2 inferInstance).1 t _ _ hb
  have ht : ∀ i, ‖Formalism.L2.PjFree.toC (t i : CAt σ)‖ ≤ B := by
    intro i
    rcases i with _ | j
    · exact (h2 w (lt_of_le_of_lt (le_max_right _ _) hw) yw hyw k x t hux hb).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 w (lt_of_le_of_lt (le_max_left _ _) hw) yw hyw k x t hux hb j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hw' : ‖Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t)‖ ≤ B ^ (∑ i, ex Dw a' n i) :=
    norm_prod_pow_le (fun i => Formalism.L2.PjFree.toC (t i : CAt σ)) (ex Dw a' n) B ht
  rw [hsc]
  change ‖(Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t) * Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) : ℂ)‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hM k x hux).trans (le_max_left _ _)) hw' (norm_nonneg _) (le_max_right _ _)

end GlobalTheory.ArcBdd
