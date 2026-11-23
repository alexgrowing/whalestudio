import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFD

variable {D : D7}

def DsigHC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1 ≤ Cl * large₂.sc.L →
    ∀ τ : D.what₂.Tau, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

theorem dsig_eq [hF : Fact DsigHC] {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hF.out D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem vv_eq_vand {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [dsig_eq hT hH hCL τ, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem fdl_of_ties {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ, vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  linarith

end Formalism.L2.SG.Pf.SzHypFD
