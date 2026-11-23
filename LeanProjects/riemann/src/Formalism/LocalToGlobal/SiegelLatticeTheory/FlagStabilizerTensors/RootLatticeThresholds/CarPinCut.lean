import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.Carrier.CarPinCut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cut_of_haar (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 F) (hGV : γ ∈ Formalism.FourierDecayAlt.B.GV k r) (hRel : Formalism.FourierDecayAlt.C6.IsRelevant B γ)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (hd : ∀ a, d a ≠ 0)
    (hZ : Formalism.QuantumDeterminants.Zhat k r B.z B.z' γ = Formalism.FourierDecayAlt.C2.monoP w d) (hGf : 0 < Formalism.QuantumDeterminants.Gf k r B.z B.z' γ)
    (hH : μ (Formalism.FourierDecayAlt.C6.Rset γ)ᶜ = 0 ∧ (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset γ, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧
      (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0) :
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut B γ μ θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) B.μSS := by
  obtain ⟨θ, hθ, hint⟩ := Formalism.FourierDecayAlt.P.orbital_integral_converges.choose_spec k r Wp Wq B γ w d A₀ F hGV hRel hd hZ hGf hA hCC
  have hMu := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq B γ w d hGV hd hZ
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Formalism.FourierDecayAlt.C6.Rset γ) (Formalism.FourierDecayAlt.D.muR B γ w) μ
    (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hGV)) hMu hH.1 hH.2.1 hH.2.2.1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hH.2.2.2
    rw [hc, h0, zero_smul]
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)
    exact this
  have hμ : μ = ENNReal.ofReal (c : ℝ) • Formalism.FourierDecayAlt.D.muR B γ w := by
    rw [hc, ENNReal.ofReal_coe_nnreal]
    rfl
  refine ⟨fun p => θ p / (c : ℝ), ?_, ?_⟩
  · rw [hμ, Formalism.L2.SG.Pf.Bridge.isNormCut_smul B γ _ hcpos]
    have e : (fun p => (c : ℝ) * (θ p / (c : ℝ))) = θ := by
      funext p; field_simp
    rw [e]
    exact hθ
  · have e : (fun p => (θ p / (c : ℝ)) • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) =
        fun p => ((c : ℝ)⁻¹ : ℝ) • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) := by
      funext p
      rw [smul_smul, div_eq_inv_mul]
    rw [e]
    exact hint.smul ((c : ℝ)⁻¹ : ℝ)

end Formalism.L2.SG.Pf.Carrier.CarPinCut

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.LocWSOf Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarFields {k r : ℕ} (U : Set (Formalism.FourierDecayAlt.B.Mat k r)) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  μ Uᶜ = 0 ∧ (∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧ (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0

def FrameAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
    (∃ (w : Equiv.Perm (Fin (D.R.rS + 1))) (d : Fin (D.R.rS + 1) → ℂ), (∀ a, d a ≠ 0) ∧
      Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
        (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
        Formalism.FourierDecayAlt.C2.monoP w d) ∧
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

theorem cutAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hF : FrameAt C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c := by
  intro γ μRv ν hP
  obtain ⟨hGV, ⟨w, d, hd, hZ⟩, hGf, hH⟩ := hF γ μRv ν hP
  exact Formalism.L2.SG.Pf.Carrier.CarPinCut.cut_of_haar _ _ _ _ A₀ hA hCC hGV hP.2.2.1 w d hd hZ hGf hH

theorem trHyp_Qc (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ))
      (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ))
      (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).1, (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.1,
    (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).2⟩

def HaarAtC (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

set_option maxHeartbeats 2000000 in

theorem frameAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hH : HaarAtC C u u' τ) : FrameAt C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨hG, hM, -, -, -⟩ := id hP
  refine ⟨Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_Qc C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ), ?_,
    gf_pos_tr (trHyp_Qc C u τ) (trHyp_Qc C u' τ) (uMat γ) hG, hH γ μRv ν hP⟩
  have hz : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam
        (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam
          (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1) :=
    Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_Qc C u τ) (trHyp_Qc C u' τ) one_ne_zero (uMat γ)
  have hm := mono_scale hM (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i)
  rw [← hz] at hm
  obtain ⟨w, d, hd, hwd⟩ := hm
  exact ⟨w, d, hd, hwd⟩

theorem cutAt_of_haar (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hH : HaarAtC C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c :=
  cutAt_of C u u' τ a b ξ ξ' c (frameAt_of C u u' τ hH) A₀ hA hCC

end Formalism.L2.SG.Pf.Carrier.CarPinTor
