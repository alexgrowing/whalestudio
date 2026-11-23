import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeVIndep

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def JointTensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p)))
            ((eQ v).symm (x v))))

theorem vJoint_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (h2 : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) :
    VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ := by
  unfold JointTensorAt at h2
  unfold VJoint
  intro p w hpw hrep hpos x
  have hex : ∃ q : X.B.I.Ginf × X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' (gamW X u u' w) q.1 q.2 := by
    have hii : i0' = i0 := funext fun v => (hi v).symm
    rw [hii]
    obtain ⟨h, h', hh⟩ := dual_frame_at_places X u u' sc i0 hsc w hrep hpos
    exact ⟨(h, h'), hh⟩
  refine Eq.trans ?_ (h2 p w hpw hrep hpos hex.choose.1 hex.choose.2 hex.choose_spec x)
  unfold unscaledOperatorAtPointRepresentative unscaledFrameConjugatedOperator
  rw [if_pos hrep, dif_pos hex]
  rfl

private theorem sign_flip_involutive {K : Type} [Ring K] (r b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K) :
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x := by
  induction x generalizing b with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨s, t⟩ := a
    have hm : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1 : K) ^ n * t) = t := by
      intro n
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [Formalism.L2.SG.DataInst.signAux, hm, ih]

private theorem exists_pt_ptOfL_of_point (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w), ?_⟩
  have hs : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)) =
      Formalism.L2.S.ptList w := sign_flip_involutive _ _ _
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  split_ifs with h
  · congr 1
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hs
  · exact (h (by rw [hs]; exact Formalism.L2.S.ptList_isPtL w)).elim

theorem vIndepAt_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hJT : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  unfold JointTensorAt at hJT
  unfold VIndepAt
  intro w hrep hpos h₁ h₁' h₂ h₂' hf₁ hf₂
  obtain ⟨p, hp⟩ := exists_pt_ptOfL_of_point (D := D) w

  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on_range (X.81 u') fun x => ?_)
  have e1 := hJT p w hp hrep hpos h₁ h₁' hf₁ x
  have e2 := hJT p w hp hrep hpos h₂ h₂' hf₂ x
  exact e1.trans e2.symm

end Formalism.L2.SG.Pf.CarrierXAll
