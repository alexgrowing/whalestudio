import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def embI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank) : WO S T :=
  HMul.hMul (C.map (incA D)) a

def ellI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : ℂ :=
  ∫ a in 𝓕, f (embI S T C a) ∂μ

def IsPerpI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * x = 0

def IsIInv (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  (∀ (a : Mx D r S.rank) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (embI S T C a) f) = ℓ f) ∧
    ∀ x, IsPerpI S T C x → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (ratW T S x) f) = ℓ f

def IsSobContO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∃ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T) (N : ℕ), IsRealFrame L ∧
    ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
        ∃ c : ℝ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) →
          ‖ℓ f‖ ≤ c * sobO ψ L N μ 𝓕 f

def FuncUniq (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D, Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, IsIInv ψ S T C ℓ → IsSobContO ψ S T ℓ →
          ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = c * ellI S T C μ 𝓕 f

def RatActO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → ∀ w, om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w)

def ParabN (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ n ∈ NI T C, ∀ f, IsThetaFunO ψ S T f → ellI S T C μ 𝓕 (om (1, n) f) = ellI S T C μ 𝓕 f

def IsAniso (S : HSp D) : Prop :=
  ∀ x : Fin S.rank → D.host.E, x ≠ 0 → ∑ i, ∑ j, star (x i) * S.gram i j * x j ≠ 0

def ConstTermAn (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsAniso S →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
      ∀ (ν : Measure (NI T C)) (𝓕N : Set (NI T C)), ν.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N ν →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ h g f, IsThetaFunO ψ S T f →
            ∫ n in 𝓕N, thetaKO om h ((n : GA D T) * g) f ∂ν = κ * ellI S T C μ 𝓕 (om (h, g) f)

end Formalism.IndefR.Eqv

end
