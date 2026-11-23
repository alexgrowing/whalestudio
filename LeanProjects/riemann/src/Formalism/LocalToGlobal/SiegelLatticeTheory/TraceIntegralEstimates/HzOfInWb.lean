import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpUnif
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchur

open MeasureTheory

noncomputable section

namespace Formalism.L2.S.Pv.NonVacuity

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S

theorem hz_of_inWb {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    ∀ a : Fin r, z (eI k r a) = 0 ∧ z (esI k r a) = 0 := by
  intro a
  refine ⟨hz _ (Or.inl (by simp [eI])), hz _ (Or.inr (by simp only [esI]; have := a.isLt; omega))⟩

variable [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem nv_side {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : 1 ≤ Cl) (τ : D.what₂.Tau) (u : D.what₂.Word) {z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ}
    (hz : inWb D.R.k D.R.rS z) (hT : 0 < Tz D.R.k D.R.rS z) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : MatKR D.R.k D.R.rS → (H →L[ℂ] H)}
    (hσ : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) σ) {Vp : Type} [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : MatKR D.R.k D.R.rS → (Vp →L[ℂ] Vp)}
    (hπ : IsColsType D u τ z π) {w0 : H} (hw0 : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σ w0)
    {μW μN : Measure (Mt D.R.k D.R.rS)} (hW : IsHaarOn (UWset D.R.k D.R.rS z) μW)
    (hN : IsHaarOn (Nset D.R.k D.R.rS) μN) :
    ∃ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0, ∃ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be z (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) π σ μW μN x y ≠ 0 := by
  obtain ⟨⟨hk1, hkev, -, -, hc, huHC, hlHC, hint, hhalf, hgb⟩, -⟩ :=
    numeric_setting_of_datum D large₂ C' Cl Cg cb Cu cT CT 1 hH hCl hCl τ u z (hz_of_inWb hz) hT
  have hk2 : 2 ≤ D.R.k := by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega
  have hσ' : IsDSHpk D.R.k D.R.rS (CayleySignature.eps48 D.R.k D.R.rS) (CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ)) σ := by
    rw [epsilon_signature_eq, lambda_highest_weight_eq]; exact hσ
  have hw0' : IsLowUnitH D.R.k D.R.rS (CayleySignature.eps48 D.R.k D.R.rS) (CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ)) σ w0 := by
    rw [epsilon_signature_eq, lambda_highest_weight_eq]; exact hw0
  obtain ⟨x, x₀, hx, hx₀, hne⟩ := Formalism.L2.SG.LitS.PfNVG.besselNVG D.R.k D.R.rS z _ (uS D u τ) (v48 D τ) (b48 D τ)
    hk2 hkev hz hT hc huHC hlHC hint hhalf hgb H σ hσ' Vp π hπ w0 hw0' μW μN hW hN
  refine ⟨σ x w0, Submodule.subset_span ⟨x, hx, rfl⟩, σ x₀ w0, Submodule.subset_span ⟨x₀, hx₀, rfl⟩, ?_⟩
  unfold Formalism.FourierDecayAlt.ThreeDimData.be Formalism.FourierDecayAlt.ThreeDimData.beInt
  rw [← Formalism.L2.S.Pv.Mom.psiGen_const]
  exact hne

variable [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem nvHyp0 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1 ≤ Cl) :
    Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 0 := by
  intro hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hl0 : l1dist lam' (lamD D τ) ≤ 0 := by simpa using hl
  have hleq := Formalism.MainNotions.S.Pv.LemmaJ.l1dist_zero hl0
  subst hleq
  have hW' := hW
  obtain ⟨hc1, hc2, hz, hz', hTz, hTz', hG, hUW, -, hUW', -, hNq, hq, -⟩ := hW'
  have hTp : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hT
  have hTp' : 0 < Tz D.R.k D.R.rS W.z' := by rw [hTz']; exact hT'

  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hNq, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').μN :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκtop
  have hDS : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ := hA.2.1
  exact ⟨nv_side hH.1 hCl τ w hz hTp hDS hc1 hw0 hUW hNH, nv_side hH.1 hCl τ w' hz' hTp' hDS hc2 hw0 hUW' hNH⟩

end Formalism.L2.S.Pv.NonVacuity
