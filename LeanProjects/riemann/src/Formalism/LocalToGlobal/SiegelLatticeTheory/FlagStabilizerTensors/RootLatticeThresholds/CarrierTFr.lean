import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

def nuE (u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (j : Fin (nfE D)) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
  Qics C (X.pl (tauE X e j)) *ᵥ X.wfr u' (tauE X e j) (i0' (tauE X e j))

def m0E (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS :=
  Formalism.L2.SG.Pf.CarrierBase.m0Of X u u' (tauE X e j) (Qcs C (X.pl (tauE X e j))) (Qics C (X.pl (tauE X e j)))

theorem isTransp_Qcs (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.IsTransp X v (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)) D.R.k D.R.rS (Qcs C (X.pl v)) (Qics C (X.pl v)) := by
  have h := isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)
  have hv : vOf X (X.pl v) = v := X.pl.symm_apply_apply v
  rw [hv] at h
  exact h

theorem frames_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) :
    Frames (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀) := by
  intro j
  have hb := Formalism.L2.SG.Pf.CarrierBase.isBaseFrame_of (X := X) (u := u) (u' := u')
    (v := tauE X e j) (hr := rfl) (hQ := isTransp_Qcs X C (tauE X e j))
    (Bs := baseOf X C u u' (tauE X e j)) (hz := rfl) (hz' := rfl) (i := i0' (tauE X e j))
  rw [← towerOf_base (baseOf X C u u' (tauE X e j)) (baseOf_μW1 X C u u' _) (baseOf_μW'1 X C u u' _) rfl] at hb
  exact hb

theorem isBuilt_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hN : ParNums (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hty : Types (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hF : Frames (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hcc : CoefCC (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hcap : CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) :
    Formalism.FourierDecayAlt.D.IsBuilt (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).χ
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).ν'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).m₀
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).top
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).A₀ := by
  have hsg := sg_of (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀) rfl
  refine ⟨⟨c.smooth, ⟨1 / 2, by norm_num, fun x hx => c.zero x hx.le⟩, c.one⟩, fun v =>
    ⟨?_, ?_, hF v, isPlace_of _ hN hty v, hcc v, hcap v⟩⟩
  · show Formalism.FourierDecayAlt.D.componentFamilySetting_ofSetting _ _ _ ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).sg v)
      _ _ _ _ _ 1 = _
    rw [hsg v]
    rfl
  · exact towerOf_norm (baseOf X C u u' (tauE X e v)) (baseOf_μW1 X C u u' _) (baseOf_μW'1 X C u u' _) rfl

theorem data_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hLA : Formalism.FourierDecayAlt.JCT.LevelsActual (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T) (j : Fin (nfE D)) :
    ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
        (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
      (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
      (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
        (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
      (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
        (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
      Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
        (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) := by
  obtain ⟨Xo, μ, L, st, hD, -⟩ := hLA j ⟨0, Nat.succ_pos _⟩
  exact ⟨Xo, μ, L, st, hD⟩

section onCut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem onCut_setting (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (hw : Formalism.FourierDecayAlt.Sz.IsWord S.G.k S.de)
    (hw' : Formalism.FourierDecayAlt.Sz.IsWord S.G.k S.de') (h1 : 1 ≤ S.l) (h2 : S.l + 2 ≤ S.G.k) (hne : S.de S.l ≠ S.de' S.l)
    (hG : Formalism.FourierDecayAlt.C.GridsOK S) :
    ∀ v, ∀ Y ∈ Set.Icc (S.cutLo v) (S.cutHi v),
      Formalism.FourierDecayAlt.I.OnCut (Formalism.FourierDecayAlt.D.parOf S v).u (Formalism.FourierDecayAlt.D.parOf S v).u' (S.l + 1) Y := by
  intro v Y hY
  obtain ⟨hlo, hhi⟩ := hY
  have hG1 := (hG v).1
  simp only [Formalism.FourierDecayAlt.C.HidaSetting.cutLo, Formalism.FourierDecayAlt.C.HidaSetting.cutHi] at hlo hhi hG1
  have hl1 : S.l + 1 ≠ 1 := by omega
  have hlk : S.l + 1 ≠ (S.G.place (S.pl v)).k := by
    show S.l + 1 ≠ S.G.k
    omega
  have hu : ∀ de : ℕ → ℝ, (S.G.place (S.pl v)).u de (S.l + 1) =
      (S.G.place (S.pl v)).v S.l - 1 / 2 - de S.l * (S.G.place (S.pl v)).Del := by
    intro de
    simp only [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg hl1, if_neg hlk, Nat.add_sub_cancel]
  simp only [Formalism.FourierDecayAlt.I.OnCut, Formalism.FourierDecayAlt.D.parOf, hu]
  have hN : (0 : ℝ) ≤ (S.Ntop : ℝ) := Nat.cast_nonneg _
  have hD : 5 ≤ (S.G.place (S.pl v)).Del := by
    nlinarith [pow_nonneg hN 3]
  rcases hw.1 S.l with h0 | h0 <;> rcases hw'.1 S.l with h0' | h0'
  · exact absurd (h0.trans h0'.symm) hne
  · right
    rw [h0, h0']
    constructor <;> linarith
  · left
    rw [h0, h0']
    constructor <;> linarith
  · exact absurd (h0.trans h0'.symm) hne

end onCut

theorem isBuiltPlace_carrierInT (Cc : ℝ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hN : ParNums (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hty : Types (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hF : Frames (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hcc : CoefCC (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hcap : CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
    (hw : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de') (hl1 : 1 ≤ l) (hl2 : l + 2 ≤ D.R.k)
    (hne : de l ≠ de' l)
    (hG : Formalism.FourierDecayAlt.C.GridsOK (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)))
    (hL : Formalism.FourierDecayAlt.JCT.LongCut Cc (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)))
    (hCA : Cc ≤ CA) (hsm : ∀ j, Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (fc j))
    (hA : Cc * ((D.R.rS : ℝ) + 1) ^ 4 *
      ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 +
        (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀) :
    Formalism.FourierDecayAlt.JCT.IsBuiltPlace Cc (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).χ
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).ν'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).m₀
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).top
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).A₀ := by
  refine ⟨(Formalism.L2.SG.Pf.CarrierSz.g_pos D).1, (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2, ?_,
    isBuilt_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀ hN hty hF hcc hcap,
    hl1, hl2, hG, hL, hCA, hsm, (by show 2 ≤ D.R.k; omega), hA, ?_⟩
  · first
      | exact Formalism.L2.SG.DataInst.unram_host D
      | exact Formalism.L2.SG.Pf.CarrierSz.unram_host D
  · exact onCut_setting _ hw hw' hl1 hl2 hne hG

theorem exists_Cc_data : ∃ Cc : ℝ, ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)
    (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ),
    Formalism.FourierDecayAlt.JCT.IsBuiltPlace Cc (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀))
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).χ
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).ν'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).m₀
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).top
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).A₀ →
    ∀ j : Fin (nfE D),
    ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
        (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
      (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
      (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
        (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
      (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
        (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
      Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
        (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) := by
  have hLAB : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := by
    first
      | exact Formalism.FourierDecayAlt.P.levels_of_built_setting
      | exact Formalism.FourierDecayAlt.P.JCT.levelsActualBuilt_proof
      | exact Formalism.FourierDecayAlt.JCT.levelsActualBuilt
      | exact Formalism.FourierDecayAlt.P.levelsActualBuilt_proof
      | exact Formalism.FourierDecayAlt.P.levelsActualBuilt
  obtain ⟨Cc, hC⟩ := hLAB
  refine ⟨Cc, ?_⟩
  intro D X θ C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀ hB j
  exact data_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀
    (hC _ _ _ _ _ _ _ _ _ _ _ hB) j

end Formalism.L2.SG.Pf.CarrierT
