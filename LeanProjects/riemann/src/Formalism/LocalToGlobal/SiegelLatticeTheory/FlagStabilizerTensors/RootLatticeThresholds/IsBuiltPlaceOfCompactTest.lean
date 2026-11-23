import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

abbrev ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInT X C u u' e he hv CA de de' l grid grid1 fc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀

def plOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hN : ParNums (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hty : Types (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) (hl2 : l + 2 ≤ D.R.k)
    (hΘ : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
        Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j))
    (j : Fin (nfE D)) : Formalism.FourierDecayAlt.KB.Pl (parE e u u' de de' j) (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)) where
  l0 := l + 1
  T := towersOf X C u u' e j
  ν' := nuE X C u' e i0' j
  m₀ := m0E X C u u' e j
  Θ := Θ j
  TP := TP j
  hl := by show 1 ≤ l + 1 ∧ l + 1 ≤ D.R.k ∧ 2 ≤ D.R.k; omega
  hT := towerOf_norm _ _ _ _
  hF := frames_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ j
  hP := isPlace_of _ hN hty j
  hΘ := hΘ j

theorem isBuiltPlace_of_compact_test (Cb Cc : ℝ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hN : ParNums (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hty : Types (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hcc : CoefCC (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hcap : CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hΘ : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
        Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j))
    (hDD : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.KB.InDDplus2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base Cb (Θ j))
    (hOk : ∀ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).Ok)
    (hw : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de') (hl1 : 1 ≤ l) (hl2 : l + 2 ≤ D.R.k)
    (hne : de l ≠ de' l)
    (hG : Formalism.FourierDecayAlt.C.GridsOK (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hR : Formalism.FourierDecayAlt.KB.GridsRich (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hL : Formalism.FourierDecayAlt.JCT.LongCut Cc (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hCA : Cc ≤ CA) (hsm : ∀ j, Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (fc j))
    (hA : Cc * ((D.R.rS : ℝ) + 1) ^ 4 *
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 +
        (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀) :
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (fun j => plOf X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ hN hty hl2 hΘ j)
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).χ A₀ := by
  obtain ⟨hg1, hg2, hun, ⟨hcut, hbv⟩, hl1', hl2', hG', hL', hCA', -, -, hA', hon⟩ :=
    isBuiltPlace_carrierInT X C Cc u u' e he hv CA de de' l grid grid1 fc c (nuE X C u' e i0')
      (m0E X C u u' e) Θ TP A₀ hN hty (frames_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      hcc hcap hw hw' hl1 hl2 hne hG hL hCA hsm hA
  refine ⟨⟨hg1, hg2, hun, hcut, fun v => hOk _, hw, hw', hl1', hl2', hne, hG', hR, hL', hCA', hA',
    fun v => ⟨rfl, hDD v, (hbv v).1, hsm v, (hbv v).2.2.2.2.1⟩⟩, fun v => (hbv v).2.2.2.2.2, hon⟩

end Formalism.L2.SG.Pf.CarrierT
