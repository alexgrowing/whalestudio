import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Easy

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem w_smooth (C : Choice X θ) (τ : D.what₂.Tau) :
    X.B.w (vOf X τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := by
  have hds := Formalism.L2.SG.Pf.dsTr C τ
  obtain ⟨hrep, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  have hy := C.y_mem τ
  have hw1 : ‖X.B.w (vOf X τ)‖ = 1 := (X.low (vOf X τ)).1
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) := ⟨P, hP, by rw [hiso _ hy, hw1], hmem⟩
  have hv0 := Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds hlow
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := WlocSk.HM.uh_inv hy
  have hsm := Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hv0 hyi
  have hinvy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (WlocSk.HM.isUnit_of_uh hy)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (C.y τ)⁻¹ (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) =
      X.B.w (vOf X τ) := by
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hyi _ hy, hinvy, hrep.1]
    rfl
  rw [e] at hsm
  exact hsm

theorem muS_haar (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (muS (C.muW u τ) (muNB D θ)) := by
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hz, hTz⟩ := zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  exact isHaarOn_muS hz hT (C.muW_haar u τ) (C.muW_one u τ) (kapN_ne_zero D hθ) (kapN_ne_top D θ)

end Easy

section Clauses

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def ContClause (C : Choice X θ) : Prop :=
  ∀ u τ, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))

def EquivClause (C : Choice X θ) : Prop :=
  ∀ u τ, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)

def ReprodClause (C : Choice X θ) : Prop :=
  ∀ u τ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
    MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (X.B.w (vOf X τ)) (Matrix.of g) •
        wT C u τ (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
    rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (X.B.w (vOf X τ))) (wT C u τ) x = wT C u τ x

def L2ChoiceCondition (C : Choice X θ) : Prop :=
  ∀ u τ, l2SG (C.nuS u τ) (wT C u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (wT C u τ) < ⊤

def EquivAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), EquivClause C

def L2ConditionAllChoices : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), L2ChoiceCondition C

def ContAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ContClause C

def ReprodAll : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ReprodClause C

theorem locFactor_of_clauses (C : Choice X θ) (hC : ContClause C) (hE : EquivClause C) (hR : ReprodClause C)
    (hL : L2ChoiceCondition C) : LocFactor C :=
  fun u τ => ⟨w_smooth C τ, (X.low (vOf X τ)).1, muS_haar C u τ, hC u τ, hE u τ, hR u τ, (hL u τ).1, (hL u τ).2⟩

theorem locFactor_of (hCA : ContAll) (hEA : EquivAll) (hRA : ReprodAll) (hLA : L2ConditionAllChoices)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (C : Choice X θ) : LocFactor C :=
  locFactor_of_clauses C (hCA D X θ C) (hEA D X θ C) (hRA D hG X θ C) (hLA D hG X θ C)

end Clauses

end Formalism.L2.SG.Pf.LocF
