import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurD
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.BesselSplitLargeGapOfBesselBranching
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.SmoothIrreducibility.SmoothVectorsIrreducible

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature Formalism.L2.SG.BesselSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace BM

theorem besselSchur'_of_dec (hJ : CompanionTheory.Lime.BM.UniqGap) (hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) (hAt : CompanionTheory.Lime.BM.AtFormAdmOne)
    (hBP : CompanionTheory.Lime.BM.BesselSplitLargeGap) (hSI : Formalism.L2.SG.BesselSplit.SmoothIrred)
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hT : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ParamTieG D Cn) :
    Formalism.MainNotions.S.Pv.Mom.BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hTw v hv
  obtain ⟨hka, hG0⟩ := hT hH
  obtain ⟨h, hgap, hok⟩ := hG0 τ lam' hl hA.1
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hTw
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, -, hcN, hl2, -, -⟩ := hA'

  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hN, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]; exact Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκtop

  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hc1ne : c1 ≠ 0 := by
    have e : (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) = 2 * kaS D := by
      unfold kaS gg; ring
    rw [hc1def, e]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hDSH

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDSd⟩ := hDSH2
  obtain ⟨S, hS⟩ := hDSd.2.2.2.2.2.1
  obtain ⟨v1, hv1S, hv10, -⟩ := hS.2.2.2.1
  set w0 : A.H := ((‖v1‖⁻¹ : ℝ) : ℂ) • v1 with hw0def
  have hw0 : IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := by
    refine ⟨PD, hPD, ?_, ?_⟩
    · rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv10)
    · exact (le_sSup (show S ∈ {S | IsKTypeOf (epsSH D.R) _ (lowK (epsSH D.R) lam') S} from hS)) (S.smul_mem _ hv1S)
  have hw0sm : IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ w0 :=
    hI.2.2.1 _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH w0
      ⟨S, hS.1, S.smul_mem _ hv1S, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hPD hS.2.1⟩
  have hsmx : ∀ x ∈ UH (Hpk D.R.k D.R.rS), IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ (A.σ x w0) :=
    fun x hx => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw0sm hx

  have hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam' h A.σ w0 W.z c1 (fun i => ((D.hcW w τ).u i : ℝ))
      W.π W.μW W.μN W.μG W.νS :=
    ⟨hHC, hDSH, hgap, hok, hw0, hz, hTpos, hc1ne, hc1, hUW, hNH, hG, hq⟩
  obtain ⟨l, hlB, hla, hlb⟩ := hAt hI _ _ _ _ h A.H A.σ w0 W.Wp W.z c1 _ W.π W.μW W.μN W.μG W.νS hSide

  have hS'0 := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  have hae0 : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS'0 hq

  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hBnz : ∃ x ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ, A.B x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hz0 : l2SG W.νS A.Φ = 0 := by
      unfold l2SG
      refine (lintegral_congr_ae ?_).trans (lintegral_zero)
      filter_upwards [hae0] with y hy
      show (‖A.B (A.σ (Matrix.of y) A.v0)‖₊ : ℝ≥0∞) ^ 2 = 0
      rw [hc _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0s hy)]
      simp
    rw [hl2] at hz0
    have hm0 : 0 < A.cN * (Module.finrank ℂ W.Wp : ℝ) := mul_pos hcN (by exact_mod_cast Module.finrank_pos)
    exact (ENNReal.ofReal_pos.2 hm0).ne' hz0
  obtain ⟨v1', hv1', v2', hv2', hne0⟩ := hBP _ _ (epsSH D.R) lam' h A.H A.σ W.z (fun _ => c1) _ W.Wp W.π W.μW W.μN
    hok.1 hgap hok.2.1 hHC hDSH hz hTpos (fun _ => hc1ne) hc1 hUW hNH ⟨A.B, by rw [psiGen_const]; exact hB1, hBnz⟩
  have hw0ne : w0 ≠ 0 := by
    intro h0; obtain ⟨-, -, hn, -⟩ := hw0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨mm, hmA, hmm⟩ := Formalism.L2.S.Pv.PeriodG.exponent_ok _ _ hok (epsSH D.R)
  obtain ⟨hI', hC1, hC2⟩ := Formalism.L2.S.Pv.PeriodG.periodContG_at (fun _ => c1) mm hHC hDSH hz hTpos hc1 hUW hNH hG hq
    hgap hmm hmA
  obtain ⟨x, hx, x₀, hx₀, hne⟩ := trans' hSI hHC hDSH hw0sm hw0ne hsmx hv1' hv2' hI' hC1 hC2 hne0
  unfold Formalism.L2.SG.BesselSplit.beOp Formalism.L2.SG.BesselSplit.beInt at hne
  rw [psiGen_const] at hne
  have hadm : Formalism.FourierDecayAlt.ThreeDimData.IsAdm A.σ w0 (A.σ x₀ w0) := Or.inl (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
  obtain ⟨-, heq⟩ := hla (A.σ x w0) (hsmx x hx) (A.σ x₀ w0) hadm
  have hlv : l (A.σ x₀ w0) ≠ 0 := by
    intro h0
    apply hne
    rw [heq, h0]
    ext y
    simp

  obtain ⟨d, hd, hSch⟩ := Formalism.MainNotions.DiscreteSeriesInnerProducts.schurH A.σ hDSH hG
  have hfd : ∀ u : A.H, u ≠ 0 → fdegH W.μG A.σ u = d :=
    fun u hu => Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegH_eq hd (fun v w v' w' => (hSch v w v' w').2) hu
  have hl0 : l 0 = 0 := by
    have := hlB.2.1 0 0 (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero)
    simpa using this
  have hlp : 0 < ‖l (A.σ x₀ w0)‖ ^ 2 := by positivity
  have hl2l : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => l (A.σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      unfold l2SG
      simp [hl0]
    · have e := hlb u hu hu0 _ hadm
      have e2 : ENNReal.ofReal (‖u‖ ^ 2 * ‖l (A.σ x₀ w0)‖ ^ 2 / fdegH W.μG A.σ u) =
          ENNReal.ofReal (‖l (A.σ x₀ w0)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
        rw [hfd u hu0, ← ENNReal.ofReal_mul hlp.le]
        congr 1
        ring
      erw [e2] at e
      exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hlp).ne' ENNReal.ofReal_ne_top).1 e

  obtain ⟨α, β, hαβ, hrel⟩ := hJ _ _ (epsSH D.R) lam' h A.H A.σ W.z (fun _ => c1) _ W.Wp W.π hok.1 hgap hok.2.1 hHC hDSH hz hTpos
    (fun _ => hc1ne) hc1 A.B l (by rw [psiGenPI_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mp hB1)
    (by rw [psiGenPI_const]; exact hlB)
  have hα : α ≠ 0 := by
    intro h0
    rcases hαβ with h1 | h1
    · exact h1 h0
    · have e := hrel _ (hsmx x₀ hx₀)
      rw [h0, zero_smul, zero_add] at e
      exact hlv ((smul_eq_zero.1 e).resolve_left h1)
  have hBl : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → A.B u = (-(β / α)) • l u := by
    intro u hu
    have e := hrel u hu
    have e2 : α • A.B u = -(β • l u) := eq_neg_of_add_eq_zero_left e
    calc A.B u = α⁻¹ • (α • A.B u) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
      _ = α⁻¹ • (-(β • l u)) := by rw [e2]
      _ = (-(β / α)) • l u := by rw [smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]

  have hS' := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  have hae : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS' hq
  have hl2B : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => A.B (A.σ g u)) = ENNReal.ofReal (‖-(β / α)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    rw [← hl2l u hu]
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hBl _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hu hy), nnnorm_smul, ENNReal.coe_mul, mul_pow,
      Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have hΦ : l2SG W.νS A.Φ = l2SG W.νS (fun g => A.B (A.σ g A.v0)) := rfl
  rw [hΦ, hl2B v hv, hl2B A.v0 hv0s, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq A.v0, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq v,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem moment_bound_schur (hJ : CompanionTheory.Lime.BM.UniqGap) (hBP : CompanionTheory.Lime.BM.BesselSplitLargeGap)
    (hSI : Formalism.L2.SG.BesselSplit.SmoothIrred) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) :
    Formalism.MainNotions.S.Pv.Mom.MomF' Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.S.Pv.Mom.momF'_of_schur_at Fm Cg cb Cu cT CT C0
    (fun Cn => Formalism.MainNotions.S.OwnEv.mono
      (fun C' Cl x i h => besselSchur'_of_dec hJ CompanionTheory.Lime.BM.inputs
        (CompanionTheory.Lime.BM.atFormAdmOne hJ) hBP hSI _ _ _ _ _ _ _ _ _ _ Cn h)
      (parameter_gap_family Fm Cg cb Cu cT CT C0 Cn))
    (fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => lowKOneAt_of_tieG _ _ _ _ _ _ _ _ _ _ Cn h)
      (parameter_gap_family Fm Cg cb Cu cT CT C0 Cn))
    Formalism.L2.SG.Pf.k_finite_smooth_bessel

theorem momF'_gap (hJ : CompanionTheory.Lime.BM.UniqGap) (hBP : CompanionTheory.Lime.BM.BesselSplitLargeGap)
    {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) :
    Formalism.MainNotions.S.Pv.Mom.MomF' Fm Cg cb Cu cT CT C0 :=
  moment_bound_schur hJ hBP CompanionTheory.D.gk.Rec.smooth_vectors_irreducible Fm Cg cb Cu cT CT C0

end BM

end Formalism.L2.S.Pv.Mom
