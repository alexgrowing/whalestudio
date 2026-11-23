import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem bSt_pos {κ : ℝ} (hκ : 0 < κ) (p : Formalism.FourierDecayAlt.C.LPt) : 0 < Formalism.FourierDecayAlt.D.bSt κ p := by
  unfold Formalism.FourierDecayAlt.D.bSt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact Finset.prod_pos fun m _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

section AtCarrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
  (he : PlaceTie X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
  (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
  (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
  (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
  (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
  (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
  (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
  (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
    List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
  (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))

local notation "PP" => CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo

def MeasPinAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → OkPt X u u' w →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ (v : InfinitePlace X.B.I.F)
      (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv →
      μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w →
    ∀ hloc : Formalism.FourierDecayAlt.D.IsLocPt (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1
      (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) ((PP).S.G.r + 1),
      (μRv.map (fun s => (h v)⁻¹ * s * h v)).map
          (fun s => Matrix.of.symm (trG ((PP).Q v) ((PP).Qi v) s)) =
        ENNReal.ofReal (Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) •
          Formalism.FourierDecayAlt.D.muR ((PP).T ((PP).τ.symm v)).base
            (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)) (hloc.2 ▸ Formalism.FourierDecayAlt.D.ptPerm _)

theorem orbVecAt_carrierOf (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hbase : ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v))
      ((PP).m₀ ((PP).τ.symm v)))
    (hMP : MeasPinAt X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0') :
    0 < sc → (PP).FromX → (PP).Base i0 i0' → (∀ j x, (PP).S.emb j (X.ιE x) = X.B.I.φ ((PP).τ j) x) →
    ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)),
      ptOfL (D := D) (D.R.rS + 1) p = some w → OkPt X u u' w →
      ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ (v : InfinitePlace X.B.I.F)
        (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv →
        μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w →
      ∀ F : Formalism.FourierDecayAlt.B.Mat (PP).S.G.k (PP).S.G.r →
          ((PP).Wq ((PP).S.pl ((PP).τ.symm v)) →L[ℂ] (PP).Wp ((PP).S.pl ((PP).τ.symm v))),
        Formalism.FourierDecayAlt.D.orbJ ((PP).T ((PP).τ.symm v)).base
                  (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))
                  ((μRv.map (fun s => (h v)⁻¹ * s * h v)).map
                    (fun s => Matrix.of.symm (trG ((PP).Q v) ((PP).Qi v) s))) F =
          (((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v)) ((PP).m₀ ((PP).τ.symm v)) F
              (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) := by
  intro hsc hFX hB hemb p w hp hw h h' hD v μRv hH hpin F
  obtain ⟨hZ, hG, hloc, hGV⟩ := orbVec_data X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo
    sc hsc i0 i0' hFX hB hemb hbase p w hp hw h h' hD v
  have hloc' : Formalism.FourierDecayAlt.D.IsLocPt (Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1
      (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) ((PP).S.G.r + 1) := hloc
  rw [hMP p w hp hw h h' hD v μRv hH hpin hloc']
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds D.R.k D.R.rS _ _ ((PP).T ((PP).τ.symm v)).base _ _ hloc hGV hZ
  have hmono := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' _ (D.R.rS + 1) hloc.2 hloc.1
  have hHaar := Formalism.FourierDecayAlt.P.radial_measure_is_haar D.R.k D.R.rS _ _ ((PP).T ((PP).τ.symm v)).base _ _ _ hGV hmono.2
    (hZ.trans hmono.1)
  have hb : 0 < Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
      (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p) := by
    refine bSt_pos ?_ _
    unfold Formalism.FourierDecayAlt.D.kapG
    have hg : (0 : ℝ) < ((PP).S.g : ℝ) := by
      show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
      exact_mod_cast Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
    exact div_pos (by positivity) (mul_pos hg (Formalism.FourierDecayAlt.P.Jx3.rd_pos D.host.E))
  have hHaar' : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset
      (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)))
      (Formalism.FourierDecayAlt.D.muR ((PP).T ((PP).τ.symm v)).base
        (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)) (hloc'.2 ▸ Formalism.FourierDecayAlt.D.ptPerm _)) := hHaar
  refine (Bridge.orbJ_smul _ _ _ F hrel hHaar' hb).trans ?_
  rw [orbVec_vecV X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀
    top A₀ Mo sc hsc i0 i0' hFX hB hemb hbase p w hp hw h h' hD v F hloc']

end AtCarrier

end Formalism.L2.SG.Pf.Carrier
