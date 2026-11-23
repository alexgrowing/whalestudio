import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.Pf.Carrier.EnergyPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def PinHyp (P : Parts X u u') (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) ∧
  IsHaarLoc (StSet (NV X u v) (NV X u' v) γ) μRv ∧ IsQuotLoc μRv ν

def trMeas (P : Parts X u u') (v : InfinitePlace X.B.I.F) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Measure (Formalism.QuantumDeterminants.Mt P.S.G.k P.S.G.r) :=
  μRv.map (fun s => Matrix.of.symm (trG (P.Q v) (P.Qi v) s))

def PinCov (P : Parts X u u') : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    PinHyp P v γ μRv ν →
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ) =
      ((P.eP v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u v).comp
        ((Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) (trMeas P v μRv)
            (P.f (P.τ.symm v))).comp
          ((P.eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] _))

def JointBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → StRel X u u' → P.FromX → P.Base i0 i0' → (∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) →
  P.Built → ∀ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
  (∀ w, OkPt X u u' w → LocPin X u u' w νl) →
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ v : InfinitePlace X.B.I.F,
    ∃ (γ' : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))), PinHyp P v γ' μRv ν ∧
      (∀ y : X.Vloc u' v,
        X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
          ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
            (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ') y) ∧
      Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ') (trMeas P v μRv) (P.f (P.τ.symm v)) =
        (((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))

def NormBridge (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.FromX → P.Built → 0 < P.S.g →
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    ∃ μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v)), PinHyp P v g μRv ν ∧
      JvX X u u' v g = (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) g) ∧
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) g) (trMeas P v μRv)
                (P.f (P.τ.symm v)))‖ =
        ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
          (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖

private theorem sum_norm_sq_apply_basis_indep {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (b : OrthonormalBasis ι ℂ Wq) (b' : OrthonormalBasis ι' ℂ Wq) (A : Wq →L[ℂ] Wp) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ‖A (b' i)‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  have key : ∀ {κ : Type} [Fintype κ] (c : OrthonormalBasis κ ℂ Wq), ∑ i, ‖A (c i)‖ ^ 2 =
      (LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint A).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq)).re := by
    intro κ _ c
    rw [LinearMap.trace_eq_sum_inner _ c, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [key b, key b']

theorem hilbertSchmidt_conj_isometry {Wp Wq : Type} {V V' : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (e : Wp ≃ₗᵢ[ℂ] V) (e' : Wq ≃ₗᵢ[ℂ] V') (A : Wq →L[ℂ] Wp) :
    hs2 ((e.toContinuousLinearEquiv : Wp →L[ℂ] V).comp
      (A.comp (e'.symm.toContinuousLinearEquiv : V' →L[ℂ] Wq))) = ‖Formalism.FourierDecayAlt.B.hsVec A‖ ^ 2 := by
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  simp only [hs2, Formalism.FourierDecayAlt.B.hsVec, PiLp.norm_sq_eq_of_L2, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
  try simp only [PiLp.toLp_apply]
  have hb : ∀ i, e'.symm (stdOrthonormalBasis ℂ V' i) = ((stdOrthonormalBasis ℂ V').map e'.symm) i := fun i => by
    rw [OrthonormalBasis.map_apply]
  simp only [hb]
  exact sum_norm_sq_apply_basis_indep _ _ A

theorem placeJ_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hR : StRel X u u') (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hνl : ∀ w, OkPt X u u' w → LocPin X u u' w νl) : PlaceJ P sc i0 i0' νl := by
  intro p w hp hrep hG h h' hD v y
  obtain ⟨γ', μRv, ν, hH, hJ, hO⟩ := hB hsc hR hFX hBase hEmb hBuilt νl hνl p w hp hrep hG h h' hD v
  rw [hJ y, hpin v γ' μRv ν hH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hO]
  rfl

theorem placeNormG_of_pin (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hpin : PinCov P) (hB : NormBridge P hr)
    (hFX : P.FromX) (hBuilt : P.Built) (hg : 0 < P.S.g) : PlaceNormG P hr := by
  intro v g cv hc hZ
  obtain ⟨μRv, ν, hH, hJ, hn⟩ := hB hFX hBuilt hg v g cv hc hZ
  rw [hJ, hpin v g μRv ν hH, hilbertSchmidt_conj_isometry, hn]

theorem jointTensor_of_pin (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u') (hLU : LocUni X u u')
    (hGP : GlobProd X u u') (hpin : PinCov P) (hB : JointBridge P sc i0 i0') (hsc : 0 < sc) (hFX : P.FromX)
    (hBase : P.Base i0 i0') (hEmb : ∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) (hBuilt : P.Built) :
    P.JointTensor sc i0 i0' νq :=
  Formalism.L2.SG.Pf.Carrier.JointFinal.joint_tensor_factorization P sc i0 i0' νq hN hR hLU hGP
    (fun νl hνl => placeJ_of_pin P sc i0 i0' hpin hB hsc hR hFX hBase hEmb hBuilt νl hνl)

end Formalism.L2.SG.Pf.Carrier.JointPin
