import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MuNEqHaarLie
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTAmpVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

abbrev gB (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MatKR D.R.k D.R.rS := trG (C.Q τ) (C.Qi τ) γ

abbrev muRB (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Measure (Mt D.R.k D.R.rS) :=
  μRv.map (fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ

theorem torS_inv_mulVec_Wb {z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : inWb D.R.k D.R.rS z) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ D.R.k D.R.rS *ᵥ z = z := by
  rw [torS_muT_inv, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, tTi_mulVec_Wb hz, Matrix.mulVec_smul,
    dMi_mulVec_wb hz, smul_smul, Complex.star_def, map_pow, Complex.conj_I, ← mul_pow, mul_neg, Complex.I_mul_I,
    neg_neg, one_pow, one_smul]

theorem zc_vOf_eq_zB_of_inWb (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    zc X C u (vOf X τ) = ((1 : ℝ) : ℂ) • zB X (C.Qi τ) u τ := by
  unfold zB at hz
  unfold zc Qic Qics zB
  rw [pl_vOf, ← Matrix.mulVec_mulVec]
  rw [torS_inv_mulVec_Wb hz]
  simp

theorem baseOf_pi (u : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    πc X C u (vOf X τ) m = piB X (C.Q τ) (C.Qi τ) u τ (tT D.R.k D.R.rS * cjI D.R.k D.R.rS (kaB D)⁻¹ 1 m *
      tTi D.R.k D.R.rS) := by
  unfold πc piB Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conjI]
  simp only [Matrix.mul_assoc]

def tN (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ENNReal := κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1))

def lamPl (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ℂ :=
  ((cO : ℂ)⁻¹ * scl * κ * ((tN D θ κ₀ * tN D θ κ₀).toReal : ℂ))⁻¹

theorem tN_toReal_ne (D : D7) (θ : ℝ) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) :
    (tN D θ κ₀ * tN D θ κ₀).toReal ≠ 0 := by
  have hd : ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (deltaN_pos (inv_pos.mpr (kaB_pos D)) one_pos)).ne'
  have hs0 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 := mul_ne_zero hk0 hd
  have hs1 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have ht0 : tN D θ κ₀ ≠ 0 := by unfold tN; exact ENNReal.div_ne_zero.mpr ⟨h0, hs1⟩
  have ht1 : tN D θ κ₀ ≠ ⊤ := by unfold tN; exact ENNReal.div_ne_top h1 hs0
  exact ENNReal.toReal_ne_zero.mpr ⟨mul_ne_zero ht0 ht0, ENNReal.mul_ne_top ht1 ht1⟩

theorem pinPlace (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)))
    (κ : ℂ)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') F γ ν =
        κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ)) (muStd (kaB D) (muRB C τ μRv))
                (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹ •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
          Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have e2 := hAmp (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB hcell
  obtain ⟨hgU, -, -, hrel, hH, hq, -⟩ := hcell
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hc : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').c =
      ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  have hBz : (baseOf X C u u' (vOf X τ)).z =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z :=
    zc_vOf_eq_zB_of_inWb C u u' τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz.1
  have hBz' : (baseOf X C u u' (vOf X τ)).z' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z' :=
    zc_vOf_eq_zB_of_inWb C u' u τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'.1
  have hBπ : (baseOf X C u u' (vOf X τ)).π =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π := by
    funext m; exact baseOf_pi C u τ m
  have hBπ' : (baseOf X C u u' (vOf X τ)).π' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π' := by
    funext m; exact baseOf_pi C u' τ m
  have hBW : (baseOf X C u u' (vOf X τ)).μW =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW := hWc
  have hBW' : (baseOf X C u u' (vOf X τ)).μW' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW' :=
    hWc'
  have hBN : (baseOf X C u u' (vOf X τ)).μN = haarLie (Nset D.R.k D.R.rS) κ₀ := hN
  have : SFinite (muRB C τ μRv) := by have := hH.1; infer_instance
  have e3 := orbJ_std (k_pos D) (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (kaB D) (kaB_pos D) hc hk0 ENNReal.ofReal_ne_top κ₀ h0 h1 (baseOf X C u u' (vOf X τ)) hBz hBz' hBπ hBπ' hBW hBW' hBN
    (gB C τ γ) hgU hrel (muRB C τ μRv) hH.2.2.1 hH.2.1 νB hq F hcut
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq C hB u u' τ γ ν hG
  have hs : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').κN = kapN D θ := rfl
  rw [hs] at e3
  refine e3.trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • Y) e2).trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • κ • Y) e1).trans ?_
  have key : ∀ (a b c : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • c • Y = (a * b * c) • Y :=
    fun a b c Y => by rw [smul_smul, smul_smul]
  refine (key _ _ _ _).trans ?_
  congr 1
  rw [lamPl, inv_inv]
  unfold tN
  ring

end Formalism.L2.SG.Pf.Carrier.CarPinTor
