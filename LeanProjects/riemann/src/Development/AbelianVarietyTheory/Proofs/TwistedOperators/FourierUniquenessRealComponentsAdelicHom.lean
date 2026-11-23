import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FourierRealPart

variable {D : D7}

theorem exists_section (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ s : (D.what₂.Tau → ℂ) → AE D, Continuous s ∧ (∀ w, finPart D (s w) = 0) ∧
      (∀ w τ, θ τ (infPart D (s w)) = w τ) ∧ (∀ a, infPart D (s fun τ => θ τ (infPart D a)) = infPart D a) ∧
      ∀ τ, Continuous fun a : AE D => θ τ (infPart D a) := by
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig D.what₂.Tau
    (tauE D) θ (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ a : AE D, (e1 a).1 = infPart D a := fun a => (he1 a).1
  have hfin : ∀ a : AE D, (e1 a).2 = finPart D a := fun a => (he1 a).2
  refine ⟨fun w => e1.symm (e.symm w, 0), hc1'.comp (hc'.prodMk continuous_const), fun w => ?_, fun w τ => ?_,
    fun a => ?_, fun τ => ?_⟩
  · rw [← hfin, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply]
    apply e.injective
    funext τ
    rw [RingEquiv.apply_symm_apply, he]
  · have h : (fun a : AE D => θ τ (infPart D a)) = fun a => e (e1 a).1 τ := by
      funext a
      rw [he, hinf]
    rw [h]
    exact (continuous_apply τ).comp (hc.comp (continuous_fst.comp hc1))

theorem dualPt_finPart {T : HSp D} {ρ : ℕ} {b : Mx D ρ T.rank} (hb : b.map (finPart D) = 0) :
    (GlobalTheory.Unf.DoubleSum.dualPt T ρ b).map (finPart D) = 0 := by
  have h : (b ⬝ giA T).map (finPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine GlobalTheory.OrientedChar.finPart_cA_eq_zero (z := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show finPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_dualPt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (z : Mx D W.rank ρ) {b : Mx D ρ W.rank}
    (hb : b.map (finPart D) = 0) :
    ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ τ, ((2 * (∑ i, ∑ j,
        θ τ (infPart D (z i j)) * θ τ (infPart D (b j i))).re : ℝ) : ℂ)) := by
  rw [GlobalTheory.Unf.DoubleSum.symplO_dualPt]
  have hfin : finPart D (z * b).trace = 0 := GlobalTheory.PhaseReal.finPart_trace z b hb
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  have h1 : ψ (Algebra.trace (AF D.host.F) (AE D) (z * b).trace) =
      psiInf D.host.F ψ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) (z * b).trace)) := congrArg ψ hT
  rw [h1, hψ.2.2 θ hθ]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [GlobalTheory.PhaseReal.theta_trace θ hθ τ]
  congr 3
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem linear_expand {K : Type} [Fintype K] [DecidableEq K] (l : (K → ℂ) →L[ℝ] ℝ) (Z : K → ℂ) :
    l Z = ∑ k, ((Z k).re * l (Pi.single k 1) + (Z k).im * l (Pi.single k Complex.I)) := by
  conv_lhs => rw [← Finset.univ_sum_single Z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : Pi.single k (Z k) = (Z k).re • (Pi.single k (1 : ℂ) : K → ℂ) + (Z k).im • (Pi.single k Complex.I : K → ℂ) := by
    ext k'
    by_cases h : k' = k
    · subst h
      simp [Complex.ext_iff]
    · simp [h]
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.FourierRealPart

open GlobalTheory.FourierRealPart in

theorem GlobalTheory.FourierRealPart.integral_preimage_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  intro D ψ hψ V V₀ W ρ d Y _ m F hF x hx hc S hS hsat
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨s, hsc, hsf, hsθ, hsinf, hcθ⟩ := exists_section θ hθ
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  classical
  let P : Mx D W.rank ρ → (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) := fun z k => θ k.2.2 (infPart D (z k.1 k.2.1))
  let sec : (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) → Mx D W.rank ρ := fun w i j => s fun τ => w (i, j, τ)
  have hP : Continuous P :=
    continuous_pi fun k => (hcθ k.2.2).comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  have hsec : Continuous sec :=
    continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun τ => continuous_apply _)
  have hmem : ∀ z, z ∈ S ↔ sec (P z) ∈ S := fun z => hsat _ _ (by
    funext i j
    exact (hsinf (z i j)).symm)
  have hpre : x ⁻¹' S = (P ∘ x) ⁻¹' (sec ⁻¹' S) := by
    ext y
    exact hmem (x y)
  rw [hpre]
  refine GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero Y m F hF _ (P ∘ x) (hP.measurable.comp hx) ?_ _ (hsec.measurable hS)
  intro l
  let B : Fin W.rank × Fin ρ × D.what₂.Tau → ℂ := fun k =>
    ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * ((l (Pi.single k 1) : ℂ) - (l (Pi.single k Complex.I) : ℂ) * Complex.I)
  let b : Mx D ρ W.rank := fun j i => s fun τ => B (i, j, τ)
  have hb : b.map (finPart D) = 0 := by
    funext j i
    exact hsf _
  have key := hc (GlobalTheory.Unf.DoubleSum.dualPt W ρ b) (dualPt_finPart hb)
  have hpt : ∀ z : Mx D W.rank ρ, Complex.exp ((l (P z) : ℂ) * Complex.I) =
      ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) := by
    intro z
    rw [psi_dualPt hψ θ hθ d z hb]
    congr 1
    have hbθ : ∀ i j τ, θ τ (infPart D (b j i)) = B (i, j, τ) := fun i j τ => hsθ _ τ
    simp only [hbθ]
    have hterm : ∀ k, (P z k).re * l (Pi.single k 1) + (P z k).im * l (Pi.single k Complex.I) =
        -(4 * Real.pi) * (P z k * B k).re := by
      intro k
      have hπ := Real.pi_ne_zero
      simp only [B, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    have h1 : l (P z) = ∑ i, ∑ j, ∑ τ, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [linear_expand l (P z), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => hterm _
    have h2 : -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re =
        ∑ τ, ∑ i, ∑ j, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      simp only [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hr : l (P z) = -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [h1, h2]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    rw [hr]
    push_cast
    ring
  simp only [Function.comp_apply, hpt]
  exact key
