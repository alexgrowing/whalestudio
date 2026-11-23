import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrsSecondCountableAbs
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def UnimodA (X : CData) : Prop := (X.I.muA X.μf).IsMulRightInvariant

instance rr_muG_right {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsMulRightInvariant :=
  ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

instance rr_muG_haar {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsHaarMeasure := by
  unfold Formalism.REAL.muG; infer_instance

theorem rr_rep_eq_rep (I : AutInst) (fund : Set I.GA) (y : I.GA) : I.rep fund y = rr_rep I.GFset fund y := rfl

theorem rr_muA_left (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant] :
    (I.muA μf).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

theorem rr_muA_right (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulRightInvariant] :
    (I.muA μf).IsMulRightInvariant :=
  Measure.prod.instIsMulRightInvariant

theorem rr_muA_sigmaFinite (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] : SigmaFinite (I.muA μf) := by
  unfold AutInst.muA; infer_instance

theorem UnimodA_of_UnimodF (X : CData) (h : UnimodF X) : UnimodA X := by
  have : X.μf.IsMulRightInvariant := h
  exact rr_muA_right X.I X.μf

theorem rr_FD_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : rr_FD (I.muA μf) (rr_GF I) fund :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem rr_IsReg_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (h : I.IsRightReg μf fund R) :
    rr_IsReg (I.muA μf) (rr_GF I) fund R := h

def RepAlg (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ ∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖

def RegData (X : CData) : Prop :=
  X.μf.IsHaarMeasure ∧ X.I.IsFundDom (X.I.muA X.μf) X.fund ∧ X.I.IsRightReg X.μf X.fund X.R

theorem RegData_of_HypB (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : RegData X :=
  ⟨hX.2.1.2.2.2.1, hX.2.1.2.2.2.2.1, hX.2.1.2.2.2.2.2.1⟩

theorem rightRegular_isometric_multiplicative (X : CData) (hd : RegData X) (hu : UnimodA X) : RepAlg X := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have h1 := rr_FD_of X.I X.μf X.fund hF
  have h2 := rr_IsReg_of X.I X.μf X.fund X.R hR
  exact ⟨fun g k => rr_mul h1 h2 g k, rr_one h1 h2, fun g F => rr_norm h1 h2 g F⟩

theorem regular_rep_coeff_measurable (X : CData) (hd : RegData X) (hu : UnimodA X) (x y : X.L2) :
    StronglyMeasurable fun g => ⟪x, X.R g y⟫_ℂ := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  exact rr_weak_meas (rr_FD_of X.I X.μf X.fund hF) (rr_IsReg_of X.I X.μf X.fund X.R hR) x y

theorem regularRep_isometric_weaklyMeasurable (X : CData) (hd : RegData X) (hu : UnimodA X) : X.RegRep :=
  ⟨(rightRegular_isometric_multiplicative X hd hu).2.2, fun x y => (regular_rep_coeff_measurable X hd hu x y).aestronglyMeasurable⟩

end Formalism.MainNotions.LeviCoordinates

end
