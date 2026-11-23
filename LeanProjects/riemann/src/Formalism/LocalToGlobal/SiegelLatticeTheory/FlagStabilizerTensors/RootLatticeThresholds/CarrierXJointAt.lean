import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJoint
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinJB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotGeo
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRelTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVecFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlockScaling
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTopOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OoQuotOfNuQPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

theorem jointTensorAt_of_carrier (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u') (hpin : JointPin.PinCov (CarrierOf I Mo))
    (hRT : JointPinJB.RelTr (CarrierOf I Mo) sc i0 i0') (hOV : JointPinJB.OrbVecAt (CarrierOf I Mo) sc i0 i0')
    (hsc : 0 < sc) (hFX : (CarrierOf I Mo).FromX) (hBase : (CarrierOf I Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf I Mo).S.emb j (X.ιE x) = X.B.I.φ ((CarrierOf I Mo).τ j) x)
    (hBuilt : (CarrierOf I Mo).Built) :
    JointTensorAt X u u' (sOf I) I.T I.fc I.ν' I.m₀ I.τ I.eP I.eQ sc i0 i0' νq :=
  JointPin.jointTensor_of_pin (CarrierOf I Mo) sc i0 i0' νq hN (JointQuot.stRel_holds X u u')
    (JointQuot.locUni_of X u u' hG) (JointQuot.globProd_of X u u' hG) hpin
    (JointPinJB.jointBridge_of_open _ sc i0 i0' hRT hOV) hsc hFX hBase hEmb hBuilt

theorem jointTensorAt_carrierInOf (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hN : NuQPin X u u' νq) (hG : JointQuot.StVGeo X u u')
    (hpin : JointPin.PinCov (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo))
    (hsc : 0 < sc)
    (hFX : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX)
    (hBase : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Base i0 i0')
    (hEmb : ∀ j x, (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.emb j
      (X.ιE x) = X.B.I.φ ((CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).τ j) x)
    (hBuilt : (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).Built) :
    JointTensorAt X u u' (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).T
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).fc
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).ν'
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).m₀
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).τ
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eP
      (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀).eQ sc i0 i0' νq := by
  have hMP : MeasPinAt X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' :=
    measPinAt_of X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc hsc i0 i0' hFX hBase hEmb
      (fun v => (hBuilt.2 _).2.2.1)
  refine jointTensorAt_of_carrier _ Mo sc i0 i0' νq hN hG hpin ?_ ?_ hsc hFX hBase hEmb hBuilt
  · intro h1 h2 h3 h4 h5
    exact relTr_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' h1 h2 h3 h4 h5
  · intro h1 h2 h3 h4 h5
    exact orbVecAt_carrierOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0'
      (fun v => (h5.2 _).2.2.1) hMP h1 h2 h3 h4

open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in
set_option maxHeartbeats 4000000 in

theorem jointTensorAt_ITcMo (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo).Built) :
    JointTensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq := by
  have hG : JointQuot.StVGeo X u u' :=
    JointQuot.stVGeo_of_sec X u u' (Formalism.L2.S.L6.UnitaryStandardVectors.stVSec_holds X u u')
  have hFX := BaseOf.fromX X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo
  have hQ : ∀ v, (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q v *
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi v = 1 :=
    fun v => (isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)).2.1
  have hBase := base_carrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) Mo i0 i0' hQ hi
    (fun j => rfl) (fun j => rfl)
  have hEmb := emb_carrierInOf e he hv C CA de de' l grid grid1 (towersOf X C u u' e) (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀
  exact jointTensorAt_carrierInOf X u u' e he hv C CA de de' l grid grid1 (towersOf X C u u' e)
    (Tz_towersOf_base_eq_T X C u u' e) fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
    (nuE X C u' e i0') (m0E X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (nuE X C u' e i0' j)
      (m0E X C u u' e j) (Θ j) (TP j)) A₀ Mo sc i0 i0' νq hN hG hpin hsc hFX hBase hEmb hBuilt

theorem TT_nonneg (I : CarrierIn X u u') (v : Fin (sOf I).f) : 0 ≤ (Formalism.FourierDecayAlt.D.parOf (sOf I) v).TT := by
  show 0 ≤ (((D.mem u).A.T : ℕ) : ℝ) * (((D.mem u').A.T : ℕ) : ℝ)
  positivity

def modelsOf (I : CarrierIn X u u') : ModelsFor (sOf I) where
  L := fun v => (Formalism.FourierDecayAlt.P.level_exists_alt (Formalism.FourierDecayAlt.D.parOf (sOf I) v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf (sOf I) v)) (Formalism.FourierDecayAlt.P.analytic_laws _ _ (TT_nonneg I v))).choose
  j := fun _ _ => 0
  lam := fun _ _ => 0
  c := Formalism.L2.SG.Pf.CarrierT.cutStd
  Cm := fun _ => 0
  σ := fun _ => 0
  Lw := fun _ _ => 0
  Ll := fun _ _ _ => 0
  Ll' := fun _ _ _ => 0

open scoped Matrix in
open Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf in
set_option maxHeartbeats 4000000 in

theorem jointTensor_compact_test (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : Formalism.L2.SG.Pf.Carrier.PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (sc : ℝ) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq)
    (hpin : JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))))
    (hsc : 0 < sc) (hBuilt : (CarrierOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      (modelsOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))).Built) :
    JointTensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).ν'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).m₀
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ sc i0 i0' νq :=
  jointTensorAt_ITcMo X C u u' e he hv CA de de' l grid grid1 fc c i0 i0' hi Θ TP A₀ (modelsOf _) sc νq hN hpin hsc hBuilt

end Formalism.L2.SG.Pf.CarrierXAll
