import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
import Formalism.HermitianCurvature.StatementJF
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObjInhab

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.EnergyCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem normSq_cTorBase (g : ℝ) :
    star (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) * (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) =
      (((g / (2 * Real.pi)) ^ 2 : ℝ) : ℂ) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  set a : ℝ := g / (2 * Real.pi) with ha
  have hk : -(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ)) = -Complex.I * (a : ℂ) := by
    rw [ha]; push_cast; field_simp
  rw [hk, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
  linear_combination (-(a : ℂ) ^ 2) * Complex.I_sq

theorem zhatTr_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
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
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX →
    0 < (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.g →
    ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
      RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) = Matrix.diagonal cv →
      trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g ∈
          Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
        Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z'
          (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
          Matrix.diagonal (Fin.snoc (α := fun _ => ℂ)
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).1
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).2) ∧
        Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
                  (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv ∈
          Formalism.FourierDecayAlt.JF.QDom D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z' := by
  intro hFX hg v g cv hcv hZ
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hgg
  set κ : ℂ := -(Complex.I * ((gg : ℝ) : ℂ)) / (2 * (Real.pi : ℂ)) with hκ
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  refine ⟨Bridge.delta_GV hTr (uMat_unitary g), ?_, ?_⟩
  · have hz2 : (T ((tauE X e).symm v)).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
    have hz2' : (T ((tauE X e).symm v)).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
    rw [hz2, hz2']
    have h1 := Bridge.zhat_cs hTr hTr' (sc := 1) one_ne_zero (Formalism.MainNotions.S.uMat g)
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u))
        (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u'))
        (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1) := h1
    rw [h1', hZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    show _ = Matrix.diagonal (Fin.snoc (α := fun _ : Fin (D.R.rS + 1) => ℂ)
      (fun a : Fin D.R.rS => ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩)
      (cv ⟨D.R.rS, by omega⟩))
    congr 1
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Fin.snoc_last, Bridge.lam_last, star_one, one_mul, mul_one]
      rfl
    · rw [Fin.snoc_castSucc]
      have hl : Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 (Fin.castSucc i) = κ ^ (D.R.rS - i.val) := by
        unfold Bridge.lam
        rw [dif_pos (show ((Fin.castSucc i : Fin (D.R.rS + 1)) : ℕ) < D.R.rS from i.2)]
        simp [cTor, hκ]
      rw [hl, star_pow]
      have hcv' : cv (Fin.castSucc i) = cv ⟨i.val, by omega⟩ := rfl
      rw [hcv', show (star κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ * κ ^ (D.R.rS - i.val) =
        (star κ * κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ by ring, hκ, normSq_cTorBase, ← Complex.ofReal_pow,
        ← pow_mul]
  · have hg0 : (0 : ℝ) < gg := by exact_mod_cast hg
    refine ⟨fun a => ?_, ?_⟩
    · show ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩ ≠ 0
      refine mul_ne_zero ?_ (hcv.1 _)
      have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg0 (by positivity)
      exact_mod_cast (pow_pos this _).ne'
    · rw [(hT _).1, (hT _).2]
      show ((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ) < Complex.normSq (cv ⟨D.R.rS, by omega⟩)
      have hG := hcv.2
      unfold Gv at hG
      rw [Dl_diagonal cv _ le_rfl, Dl_diagonal cv _ (Nat.le_succ _),
        Formalism.L2.SG.Pf.CarrierTop.prod_castLE_succ cv, norm_mul] at hG
      have hP : 0 < ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖ :=
        norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hcv.1 _)
      have hlast : cv (Fin.last D.R.rS) = cv ⟨D.R.rS, by omega⟩ := rfl
      rw [hlast] at hG
      rw [Complex.normSq_eq_norm_sq]
      unfold Tw at hG
      nlinarith [sq_nonneg ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖]

end Formalism.L2.SG.Pf.Carrier
