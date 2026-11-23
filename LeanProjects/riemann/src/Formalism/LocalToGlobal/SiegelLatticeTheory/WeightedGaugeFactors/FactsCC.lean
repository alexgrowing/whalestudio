import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CapCoefGen

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem coefCap_carrierInT_own (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h) :
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀) := by
  intro j0 Y g hg
  obtain ⟨j, rfl⟩ : ∃ j : Fin (nfE D), j = j0 := ⟨j0, rfl⟩
  obtain ⟨g, rfl⟩ : ∃ g' : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, g' = g := ⟨g, rfl⟩
  set w := tauE X e j with hw
  set τ := e (plE D j) with hτ
  have hpl : X.pl w = τ := by
    show X.pl (X.pl.symm (e (plE D j))) = _
    exact Equiv.apply_symm_apply _ _
  obtain ⟨hQP, hPQ, hH, -⟩ := isTransp_Qcs X C w
  rw [hpl] at hQP hPQ hH
  set P := Qcs C τ
  set Q := Qics C τ
  set σ := X.B.σ w
  set ε := X.B.I.ε w
  have hσ : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := (X.ds w).2.2.1
  have hbm : (b j : X.B.H w) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ := Formalism.MainNotions.BesselDiscreteSeries.mem_smD_of_smoothVecs (hb j)
  set T0 : X.Vloc u' w →L[ℂ] X.Vloc u w := (innerSL ℂ (ξ' j)).smulRight (ξ j)
  have hF : ∀ h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      hᴴ * (Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P) * h = Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P →
      fcT X C e u u' a b ξ ξ' cc j h =
        (inner ℂ (a j) (σ (P * h * Q) ((⟨b j, hbm⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : X.B.H w))) • (cc j • T0) := by
    intro h _
    rw [fcT_eq]
    unfold Formalism.MainNotions.S.Pv.BetaCut.coefM
    rw [smul_smul, mul_comm, ← smul_smul]
    congr 1
    ext y
    simp [T0, smul_smul, mul_comm]
    rfl
  have hg' : gᴴ * (Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P) * g = Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P := by
    have : gᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hg
    rw [← hH] at this; exact this
  obtain ⟨hh, hgapw, hthr⟩ := hgap w
  have hcap := Formalism.MainNotions.BesselDiscreteSeries.gapped_infinitesimal_character X.B.I.n ε (X.B.lam w) (X.B.H w) σ (hHC w) (X.ds w) hh hgapw hthr
    (b j) (hb j) (Y : ℂ)
  rw [Formalism.MainNotions.BesselDiscreteSeries.actU_qdet hσ _ (b j) hbm] at hcap
  have hn : (X.B.I.n : ℂ) = ((Formalism.FourierDecayAlt.Q.mdim D.R.k D.R.rS 0 : ℕ) : ℂ) := by
    rw [X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R]
    unfold Formalism.FourierDecayAlt.Q.mdim
    simp
  show Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (Formalism.FourierDecayAlt.Q.uC D.R.k D.R.rS 0 (Y : ℂ))
    (fcT X C e u u' a b ξ ξ' cc j) g = _
  rw [← hH]
  refine (Formalism.L2.SG.Pf.CapCoef.capelliH_cf_rect (ε := ε) (σ := σ) hσ hQP hPQ (a j) (cc j • T0) ⟨b j, hbm⟩ _ hF _ hg').trans ?_
  have hu : Formalism.FourierDecayAlt.Q.uC D.R.k D.R.rS 0 (Y : ℂ) = (Y : ℂ) + ((X.B.I.n : ℂ) - 1) / 2 := by
    unfold Formalism.FourierDecayAlt.Q.uC; rw [hn]
  rw [hu, hcap, map_smul, inner_smul_right, ← smul_smul, ← hF g hg']
  congr 1

  rw [Formalism.MainNotions.BridgeLemma.capelliPoly_ofReal]
  congr 1
  show ∏ s, ((Y : ℝ) + X.B.lam w s) = ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).P Y
  rw [Formalism.L2.SG.Pf.SzHypOf.gOf_place, Formalism.MainNotions.BridgeLemma.cfg_P]
  simp only [X.lam_eq w, hpl]
  exact Fintype.prod_equiv (finCongr X.n_eq) _ _ (fun i => rfl)

instance factCoefCapAll : Fact CoefCapAll :=
  ⟨by
    intro D X θ C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap
    exact coefCap_carrierInT_own X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap⟩

end Formalism.L2.SG.Pf.CarrierT
