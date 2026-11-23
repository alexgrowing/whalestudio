import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPointsStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolEqPf
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDuaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainNormalisingConstantsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoordsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicativeStatement

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom
open Formalism.L2.SG.PoincareInHH.PoincareSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formallyUnramified_host (D : D7) : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  have : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  infer_instance

theorem cancel_conj {m : ℕ} (A M N : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A.det)
    (h : A * M * A⁻¹ = A * N * A⁻¹) : M = N := by
  have key : ∀ Z : Matrix (Fin m) (Fin m) ℂ, A⁻¹ * (A * Z * A⁻¹) * A = Z := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  rw [← key M, h, key N]

theorem isDomN (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    GlobalTheory.SnMass.IsDomN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) (Pc X u) (Ac X C)
      (Gm D '' (trX X C '' Y.FN u)) := by
  obtain ⟨hmeas, hex, huniq⟩ := Y.FN_fund u
  obtain ⟨hsurj, hinj, hmul⟩ := GlobalTheory.T.transport_real_points_bijective_multiplicative D X θ C
  obtain ⟨h8a, h8b⟩ := GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords D X θ C u
  have hgrp := Formalism.L2.SG.Pf.IdMeet.noinfEqC_holds D X u Y.hK
  have hA : ∀ w, IsUnit (Ac X C w).det := by
    intro w
    have h1 := (GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u).1 w
    have h2 := (GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X).1.2
    have e : ((Jc X).map w.embedding).det = w.embedding (Jc X).det := by rw [RingHom.map_det]; rfl
    have h3 : ((Jc X).map w.embedding).det ≠ 0 := by rw [e]; exact (map_ne_zero _).2 h2
    rw [← h1, Matrix.det_mul, Matrix.det_mul] at h3
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h3)
  refine ⟨GlobalTheory.T.measurableSet_transported_real_points_image D X θ C _ hmeas, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj x hx
  obtain ⟨s, hs, hsg⟩ := hex g
  obtain ⟨γ, hγ, hc⟩ := h8b s hs
  refine ⟨γ, ⟨hγ, trX X C (s * g), ⟨s * g, hsg, rfl⟩, ?_⟩, ?_⟩
  · funext w
    rw [hc w, ← hmul]
    simp
  · rintro γ' ⟨hγ', y, ⟨f, hf, rfl⟩, hy⟩
    obtain ⟨s', hs', hc'⟩ := h8a γ' hγ'
    have hfe : f = s' * g := by
      apply hinj
      funext w
      have := congrFun hy w
      simp only at this ⊢
      rw [this, hc' w, ← hmul]
      simp
    have hmem : s' * s⁻¹ ∈ NOinf X u := by
      rw [hgrp] at hs hs' ⊢
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ hs)
    have hss : s' * s⁻¹ = 1 := huniq (s * g) hsg _ hmem (by rw [show s' * s⁻¹ * (s * g) = s' * g by group, ← hfe]; exact hf)
    have hs'e : s' = s := by rw [mul_inv_eq_one] at hss; exact hss
    subst hs'e
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    have hm := cancel_conj _ _ _ (hA w) ((hc' w).trans (hc w).symm)
    refine Matrix.ext fun i j => w.embedding.injective ?_
    have := congrFun (congrFun hm i) j
    simpa only [Matrix.map_apply] using this

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D X Y θ C u
  obtain ⟨hs, hnum⟩ := GlobalTheory.T.fundamental_domain_normalising_constants D
  obtain ⟨hH, hSD⟩ := GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X
  obtain ⟨hF, hDu, hT⟩ := GlobalTheory.T.wordFrame_dualTuple_gram_integrality D X u
  obtain ⟨hM, hAd⟩ := GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u
  have hI := GlobalTheory.T.covolume_integral_unipotentRadical_real_points D.host.F D.host.E D.sp.cm.sig D.R.k D.R.rS (Jc X) (Lc X) (Pc X u) (fc X) (Tc u)
    (Ac X C) (sc D) (GlobalTheory.AdelicU.isCMExt_host D) (formallyUnramified_host D) hH hSD hF hDu hT hM hs hAd
  have h1 := hI.2 _ (isDomN D X Y θ C u)
  have hv : 0 ≤ 2 * D.host.v := by unfold Host.v Host.rdE; positivity
  change (Measure.pi _ (trX X C '' Y.FN u)).toReal = _
  rw [← GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image D, h1, hnum, ENNReal.toReal_ofReal (Real.rpow_nonneg hv _)]

end GlobalTheory.CovDom
