import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERHaarPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem fundG_hs_sub_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A - A') C = B.hsInner A C - B.hsInner A' C := by
  unfold B.hsInner
  simp only [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_sub, inner_sub_right]

theorem fundamental_domain_group : FundG := by
  intro k r Wp Wq _ _ _ _ _ _ D A A' hA hA' hI g₀ hg₀
  have hμ := D.haarG
  have : IsFiniteMeasureOnCompacts D.μG := ⟨hμ.finite_compact⟩
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1
  have hG0 : 0 < Gf k r D.z D.z' g₀ := hg₀.2
  by_contra hne
  set C : Wq →L[ℂ] Wp := A g₀ - A' g₀ with hC
  have hC0 : C ≠ 0 := sub_ne_zero.2 hne
  have hvC : B.hsVec C ≠ 0 := fun h0 => hC0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
  set u : B.Mat k r → ℝ := fun x => (B.hsInner (A x) C - B.hsInner (A' x) C).re with hu
  have hu0 : u g₀ = ‖B.hsVec C‖ ^ 2 := by
    show (B.hsInner (A g₀) C - B.hsInner (A' g₀) C).re = _
    rw [← fundG_hs_sub_left]
    unfold B.hsInner
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpos0 : 0 < u g₀ := by rw [hu0]; positivity
  have huc : ContinuousOn u (B.GV k r) := by
    have hhs := Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)
    have h1 : ContinuousOn (fun x => B.hsInner (A x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A x, C)) (hA.prodMk continuousOn_const)
    have h2 : ContinuousOn (fun x => B.hsInner (A' x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A' x, C)) (hA'.prodMk continuousOn_const)
    exact Complex.continuous_re.comp_continuousOn (h1.sub h2)

  have hgf := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z'
  obtain ⟨ε1, hε1, h1⟩ := Metric.continuousOn_iff.1 huc g₀ hg₀G (u g₀ / 2) (by positivity)
  obtain ⟨ε2, hε2, h2⟩ := Metric.continuous_iff.1 hgf g₀ (Gf k r D.z D.z' g₀ / 2) (by positivity)
  set ε := min ε1 ε2 with hε
  have hεpos : 0 < ε := lt_min hε1 hε2
  have hgood : ∀ x ∈ B.GV k r, dist x g₀ < ε → 0 < u x ∧ x ∈ B.GPos D := by
    intro x hx hd
    have hd1 := h1 x hx (lt_of_lt_of_le hd (min_le_left _ _))
    have hd2 := h2 x (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq] at hd1 hd2
    refine ⟨by linarith [(abs_lt.1 hd1).1], hx, ?_⟩
    show 0 < Gf k r D.z D.z' x
    linarith [(abs_lt.1 hd2).1]

  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  have hβd : ∀ x : B.Mat k r, β x ≠ 0 → dist x g₀ < ε / 2 := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx (β.zero_of_le_dist (by rw [hβout]; exact hc))
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • C with hφ
  have hφs : ContDiff ℝ ∞ φ := (Complex.ofRealCLM.contDiff.comp β.contDiff).smul contDiff_const
  have hφc : HasCompactSupport φ := (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hφsupp : B.SuppIn (B.GPos D) φ := by
    intro x hx
    have hsub : {g | g ∈ B.GV k r ∧ φ g ≠ 0} ⊆ Metric.closedBall g₀ (ε / 2) ∩ B.GV k r := by
      rintro g ⟨hgG, hg⟩
      refine ⟨?_, hgG⟩
      have hβ0 : β g ≠ 0 := fun h0 => hg (by simp [hφ, h0])
      exact Metric.mem_closedBall.2 (le_of_lt (hβd g hβ0))
    have hGc : IsClosed (B.GV k r) := Formalism.FourierDecayAlt.P.B7.isClosed_GV
    have hcl : IsClosed (Metric.closedBall g₀ (ε / 2) ∩ B.GV k r) := Metric.isClosed_closedBall.inter hGc
    have hx' := closure_minimal hsub hcl hx
    exact (hgood x hx'.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hx'.1) (by linarith))).2
  have hEq := hI φ (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_of_contDiff hφs ⊤ _) hφc hφsupp

  have hGc' : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := Formalism.FourierDecayAlt.P.B7.isClosed_GV
  have hK : IsCompact ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) := hφc.isCompact.inter_left hGc'
  have hint : ∀ A₁ : B.Mat k r → (Wq →L[ℂ] Wp), ContinuousOn A₁ (B.GV k r) →
      Integrable (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x))) D.μG := by
    intro A₁ hA₁
    have hof : Continuous (fun x : Mt k r => (Matrix.of x : B.Mat k r)) := continuous_id
    have hc : ContinuousOn (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)))
        ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) :=
      (Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn
        (f := fun x : Mt k r => (A₁ (Matrix.of x), φ (Matrix.of x)))
        ((hA₁.comp hof.continuousOn (fun x hx => hx.1)).prodMk (hφs.continuous.comp hof).continuousOn)
    refine (hc.integrableOn_compact hK).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG hxK
    have hx : x ∉ tsupport φ := fun h => hxK ⟨hxG, h⟩
    show B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)) = 0
    have hz : φ (Matrix.of x) = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hz]
    exact Formalism.FourierDecayAlt.P.B5.hs_zero_right _
  have i1 := hint A hA
  have i2 := hint A' hA'

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * u (Matrix.of x) with hh
  have hpt : ∀ x : Mt k r, (B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) -
      B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x))).re = h x := by
    intro x
    simp only [hh, hu, hφ, Formalism.FourierDecayAlt.P.B5.hs_smul_right, Complex.conj_ofReal, ← mul_sub, Complex.re_ofReal_mul]
  have hintR : Integrable h D.μG :=
    (i1.sub i2).re.congr (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hzero : ∫ x, h x ∂D.μG = 0 := by
    have e := integral_re (i1.sub i2)
    simp only [Pi.sub_apply] at e
    rw [integral_sub i1 i2, hEq, sub_self, map_zero] at e
    rw [← e]
    exact integral_congr_ae (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hnn : 0 ≤ᵐ[D.μG] h := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG
    show 0 ≤ β (Matrix.of x) * u (Matrix.of x)
    by_cases hb : β (Matrix.of x) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg β.nonneg (hgood _ hxG (by linarith [hβd _ hb])).1.le
  have hae : h =ᵐ[D.μG] 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hintR).1 hzero

  have hO : IsOpen {x : Mt k r | 0 < β (Matrix.of x)} := isOpen_lt continuous_const β.continuous
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < β (Matrix.of x)} := by
    show 0 < β g₀
    rw [β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)]
    exact one_pos
  apply Formalism.FourierDecayAlt.P.CutMP.ER.haar_open_pos hμ hO (g₀ := g₀) hg₀G hg₀O
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae, Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx0 hxG hxO
  have hb : 0 < β (Matrix.of x) := hxO
  have hpos : 0 < h x := mul_pos hb (hgood _ hxG (by linarith [hβd _ hb.ne'])).1
  rw [hx0] at hpos
  exact lt_irrefl _ hpos

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
