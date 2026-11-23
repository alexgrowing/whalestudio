import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : Prop where
  theta : IsThetaFunO ψ V W f
  ne : f ≠ 0
  vac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f

def ptOf {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

def expS (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) : ℚ := -(D.hc τ).e k - (if Even (k : ℕ) then 1 / 2 else 0)

def expT (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) : ℚ := -(D.hc τ).e k - (if Even (k : ℕ) then 0 else 1 / 2)

def signed (l₁ l₂ : List ℚ) (c : ℚ) : SPar :=
  (l₁.map fun x => (x + c, true)).toFinset ∪ (l₂.map fun x => (x + c, false)).toFinset

def ChainPar (D : D7) (k : Fin D.R.m) : Prop :=
  ∀ τ, ∃ al be ga de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataAR D.R.t al be ga de ∧
    (∀ e ∈ al ++ be ++ ga ++ de, ((D.R.t : ℚ) + 3) / 2 ≤ |e|) ∧
    parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (expT D k τ) ∧
    parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (expS D k τ)

def IsStepWeil (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χS χT ω ∧
    ∀ τ, HasInfExp D χS τ (expS D k τ) ∧ HasInfExp D χT τ (expT D k τ)

def ItPair (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (M : DSModel V (parB (Ptw D) k)) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It

def ItLine (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (M : DSModel V (parB (Ptw D) k)) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
      ∀ It It' : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
        IsItW θ M M' ω (ptOf ψ θ M M' f) It → IsItW θ M M' ω (ptOf ψ θ M M' f) It' → ∃ c : ℂ, It' = c • It

def LiftInteg (D : D7) : Prop :=
  ∀ (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ f F, IsThetaFunO ψ V W f → IsAutFunSm θ W F → IsCuspFun W F →
      ∀ g, IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν

def LiftCusp (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (_M : DSModel V (parB (Ptw D) k)) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ ω, IsStepWeil k ψ V W ω → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure →
      IsFundamentalDomain (GQ W) 𝓕 ν → ∀ J χ, ∀ F ∈ MultT θ M' J χ, ∀ v f, IsThetaFunO ψ V W f →
        IsCuspFun V (Lift.liftInt ν 𝓕 (thetaKO ω) f (F v))

def IoPair (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (M : DSModel V (parB (Ptw D) k)) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f) →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ))), C ≤ MultT θ M' J' χ' →
      Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ)

section Top

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def StepsOK : Prop :=
  (∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
    IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)) ∧
  ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧
    IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t)

def LawsOK : Prop :=
  (∀ t k, k + 1 < D.R.m → ∀ κ ∈ levS _ (R.βY k) (R.datYt t k R.triv), κ ∈ GfC (Yc D k) ∧
    R.ωY t k (κ, 1) (R.vY t k) = levChi _ (R.βY k) (R.datYt t k R.triv) κ • R.vY t k) ∧
  ∀ t, ∀ κ ∈ levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv), κ ∈ GfC (Yc D (D.R.m - 1)) ∧
    R.ωX t (κ, 1) (R.vX t) = levChi _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) κ • R.vX t

def EndForms : Prop :=
  ∀ t, ∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ

def ItYSt : Prop :=
  ∀ k, k + 1 < D.R.m → ∃ y, ∀ t, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) y

def ItXSt : Prop :=
  ∃ y, ∀ t, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t) (R.ptX t) y

def IoYSt : Prop :=
  ∀ t k, k + 1 < D.R.m → Lift.IoExists (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
    (R.CC t (k + 1)) (R.CC t k)

def IoXSt : Prop :=
  ∀ t, Lift.IoExists (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX
    (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (R.CC t (D.R.m - 1))

end Top

end GlobalTheory.Chain

end
