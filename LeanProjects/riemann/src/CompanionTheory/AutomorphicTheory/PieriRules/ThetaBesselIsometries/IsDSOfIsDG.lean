import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

section gap

variable {k r : ℕ}

structure Rep.IsDG (R : Rep k r) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) : Prop where
  hc : Formalism.QuantumDeterminants.IsHCParam mu
  ds : PI.UpqRep.IsDSHpk k r ε mu R.σ
  gap : ∃ h, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ GapOK k r h

theorem _root_.GlobalTheory.isDS_of_isDG {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε mu) : R.IsDS ε mu := ⟨h.1, h.2⟩

def IsFamG (lam : Fin (2 * r + k + 1) → ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) : Prop :=
  ∀ ν, ∑ a, (ν a).natAbs ≤ q0 → (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))

end gap

def RankOneG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (R : Rep k r)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    R.IsDG ε lam → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u π →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    ∃ L : R.H → Wp, ∀ w ∈ R.sm, ∀ v ∈ R.sm,
      Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN) ∧
      be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w)

def InputsG : Prop := DecLow ∧ DecInf ∧ PI.KFinSmooth ∧ RankOneG

def InfCharG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)), (∃ Q, PI.UpqRep.IsCayleyU k r ε Q) →
    (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ GapOK k r h) → Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl (2 * r + k + 1))
          (Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

def DSExistG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam mu →
    (∃ P, PI.UpqRep.IsCayleyU k r ε P) → (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ GapOK k r h) →
    ∃ R : Rep k r, R.IsDG ε mu

def ZuckG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r),
    (∀ ν, n1 ν ≤ q0 → (R ν).IsDG ε (fun a => lam a + (ν a : ℝ))) → ∀ ν,
    (∀ l, n1 ν + l ≤ q0 →
      ∃ io pr, TensRaw (cmp l) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr) ∧
    (n1 ν + 1 ≤ q0 → ∃ io pr, TensRaw dualM (R ν) (fun s => R (ν - Pi.single s 1)) io pr)

def PoulsenG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDG ε mu → R'.IsDG ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)

def HCFdegG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool), (∃ Q, PI.UpqRep.IsCayleyU k r ε Q) → ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Mx k r → (H →L[ℂ] H)), (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ GapOK k r h) →
      PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
      PI.UpqRep.IsFdeg (PI.UpqRep.muG ε) σ (c * PI.UpqRep.fdegHC lam)

def HypsG : Prop :=
  InputsG ∧ PI.SmoothCyc ∧ InfCharG ∧ DSExistG ∧ ZuckG ∧ PoulsenG ∧ HCFdegG

section side

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def SetupG {k r : ℕ} [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  Num k r lam u b bv ga h q0 ∧ IsFamG lam q0 R ∧ SideG k r z π u μW μN μG νq ∧ SideFam z π μW μN μG q0 R l dg

end side

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

structure SupG (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFamG lam q0 R
  left : haveI := FiniteDimensional.complete ℂ Wp
    SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg
  right : haveI := FiniteDimensional.complete ℂ Wq
    SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg
  nz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)
  coef : ∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) →
    IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν
  zero : ∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0
  tau_zero : ∀ ν I, J ν = 0 ∨ J (ν + eZ I) = 0 → tau ν I = 0
  tau_eq : ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        tau ν I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)

end BranchingSupport
