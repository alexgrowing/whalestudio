import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TheoremBFixedOfExpansionLemmaJ

noncomputable section

open scoped Classical
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)
  (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))

def aT (τ : D.what₂.Tau) : ℂ := (((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ

def K0 : ℝ := (∏ τ, Complex.normSq (aT u u' C hB τ)) / Formalism.L2.SG.Pf.OOCore3.sclV Y u u'

def LocUniqP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) → ∀ τ,
      Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) =
        Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J ((νl w (vOf X τ)).map
          (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ)))) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ))

def MeasP : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau),
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) ((gamW X u u' w) (vOf X τ)) * Matrix.of x)))
      ((νl w (vOf X τ)).map (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ))))

private theorem hsNormSq_real_smul' {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsNormSq (c • A) = Complex.normSq c * Formalism.MainNotions.S.hsNormSq A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← Finset.mul_sum]
  rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul]

theorem locNormPK_of (hU : LocUniqP u u' C hB νl) (hM : MeasP u u' C hB νl) (hK : 0 < K0 Y u u' C hB)
    (hW : Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (K0 Y u u' C hB)) : Formalism.L2.SG.Pf.OOCore3.LocNormPK Y u u' C hB large₂ C1 νl := by
  intro w hrow hrep
  refine ⟨K0 Y u u' C hB, hK, hW, ?_⟩
  have hs : Formalism.L2.SG.Pf.OOCore3.sclV Y u u' ≠ 0 := by
    intro h0
    unfold K0 at hK
    rw [h0, div_zero] at hK
    exact lt_irrefl _ hK
  have hfac : ∀ τ, Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) = Complex.normSq (aT u u' C hB τ) *
      Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Jv (νl w (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) ((gamW X u u' w) (vOf X τ))) := by
    intro τ
    rw [hU w hrow hrep τ]
    exact (congrArg Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.LocJEq.locJ_map_eq (C := C) (hB := hB) u u' τ _ _
      (hM w τ))).trans (hsNormSq_real_smul' _ _)
  unfold Formalism.L2.SG.Pf.JointAmplitudePoints.localAmplitudeProduct
  simp only [hfac, Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp X.pl.symm]
  unfold vOf K0
  field_simp

end Formalism.L2.SG.Pf.LocNorm
