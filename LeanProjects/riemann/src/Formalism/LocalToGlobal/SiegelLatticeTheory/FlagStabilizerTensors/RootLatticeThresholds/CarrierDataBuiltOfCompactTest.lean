import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTopOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open Formalism.L2.SG.Pf.Choice

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem compat_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) :
    Formalism.L2.SG.DataInst.Compat (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) u u' := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Formalism.MainNotions.LatticeGluingRadicals.d_card D⟩

theorem builtFromX_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) :
    BuiltFromX X (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) u u'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ := by
  intro v
  have hw : tauE X e ((tauE X e).symm v) = v := Equiv.apply_symm_apply _ v
  have hT := transpC X C v
  refine ⟨?_, ?_, ?_, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · have h := isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)
    rwa [show vOf X (X.pl v) = v from X.pl.symm_apply_apply v] at h
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z = zc X C u v
    rw [towersOf_base]
    show zc X C u (tauE X e ((tauE X e).symm v)) = zc X C u v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z' = zc X C u' v
    rw [towersOf_base]
    show zc X C u' (tauE X e ((tauE X e).symm v)) = zc X C u' v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π m = _
    rw [towersOf_base]
    exact (cast_conj X C u (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π' m = _
    rw [towersOf_base]
    exact (cast_conj X C u' (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.μG = μGc X C v
    rw [towersOf_base]
    show μGc X C (tauE X e ((tauE X e).symm v)) = μGc X C v
    rw [hw]
  · show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (towersOf X C u u' e ((tauE X e).symm v)).base.z} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((towersOf X C u u' e ((tauE X e).symm v)).base.μN.prod
          (towersOf X C u u' e ((tauE X e).symm v)).base.μW).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [towersOf_base]
    show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zc X C u (tauE X e ((tauE X e).symm v)))} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS).prod (μWc X C u (tauE X e ((tauE X e).symm v)))).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [hw]
    exact muS_loc (n_eq' X) (X.B.I.ε v) hT.1 hT.2.1 hT.2.2.1 (zc_spec X C u v).1 (zc_pos X C u v)
      (μW_exists X C u v).choose_spec.1 (μW_exists X C u v).choose_spec.2 (Formalism.FourierDecayAlt.P.Dx2.MN.haar D.R.rS)

theorem baseFromX_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) (hi : ∀ v, i0 v = i0' v) :
    BaseFromX X (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) u u' i0 i0'
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi
      (nuE X C u' e i0') (m0E X C u u' e) :=
  Formalism.L2.SG.Pf.CarrierBase.baseFromX_of X u u' _ i0 i0' _ _ _ (fun v => (isTransp_Qcs X C v).2.1) hi

theorem topTie_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (sc : ℝ) (i0 i0'' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hPG : Formalism.FourierDecayAlt.C.PropGram (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (VtPt X u u' sc i0 i0'' FdN FdN' νq)) :
    TopTie X (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) u u' sc i0 i0'' FdN FdN' νq
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ :=
  Formalism.L2.SG.Pf.CarrierTop.topTie_of X _ u u' sc i0 i0'' FdN FdN' νq _ hPG (fun j x => embE_apply X e j x)
    (G_sOf _)

theorem carrierDataBuilt_of_compact_test (Cb Cc C₆ : ℝ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
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
    (hB : Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (fun j => plOf X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ hN hty hl2 hΘ j)
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).χ A₀)
    (hSB : Formalism.FourierDecayAlt.JCT.SliceBudget (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) A₀)
    (hcut : ∀ v, C₆ * ((D.R.k : ℝ) * (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)).Ntop *
        ((D.R.rS : ℝ) + 1) ^ 2 +
        ((sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)).Ntop : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤
      (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)).cutHi v -
        (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)).cutLo v)
    (hVt : Formalism.FourierDecayAlt.JCT.VtTensor (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (nuE X C u' e i0') (m0E X C u u' e) (VtPt X u u' sc i0 i0' FdN FdN' νq))
    (hPG : Formalism.FourierDecayAlt.C.PropGram (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (VtPt X u u' sc i0 i0' FdN FdN' νq))
    (hVJ : VJoint X (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) u u' sc i0 i0' νq
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (nuE X C u' e i0') (m0E X C u u' e)
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ)
    (hE : ∀ (L : ∀ v : Fin (nfE D), Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (parE e u u' de de' v)
        (Formalism.FourierDecayAlt.MA.DQ (parE e u u' de de' v))) D.R.rS)
      (j : ∀ v : Fin (nfE D), Formalism.FourierDecayAlt.M.Ty (parE e u u' de de' v) →
        Formalism.FourierDecayAlt.MA.SmQ D.R.rS (parE e u u' de de' v).TT)
      (lam : ∀ v : Fin (nfE D), Fin (D.R.k + 2 * D.R.rS + 1) → ℝ) (Cm σ : Fin (nfE D) → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
        (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).T
        (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
        (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel (sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) j Cm v) = jn)
    (hi : ∀ v, i0 v = i0' v) :
    CarrierDataBound X u u' sc i0 i0' FdN FdN' νq jn CA (Formalism.L2.SG.SpectralTiesReal.gOf D e) de de' l C₆ Cc Cb :=
  ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀),
    fun j => plOf X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ hN hty hl2 hΘ j,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).χ, A₀, c,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).τ,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Q,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).Qi,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eP,
    (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).eQ,
    rfl, rfl, rfl, rfl, rfl, compat_ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀, hB, hSB, rfl,
    hcut, hVt, builtFromX_ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀,
    baseFromX_ITc X C u u' e he hv CA de de' l grid grid1 fc c i0 i0' Θ TP A₀ hi,
    topTie_ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ sc i0 i0' FdN FdN' νq hPG, hVJ, hE⟩

end Formalism.L2.SG.Pf.CarrierT
