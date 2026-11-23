import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (D) in

def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

theorem labE_conj (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def ArchLab.flip (A : ArchLab D) : ArchLab D := ⟨A.perm, !A.side⟩

def ArchLab.pos (A : ArchLab D) : ArchLab D := ⟨A.perm, true⟩

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ

variable (D) in

def baseLab : ArchLab D := ⟨Equiv.refl _, true⟩

theorem isLabOf_base : IsLabOf D.what₂.embLL (baseLab D) := by
  intro τ
  rw [labE_base]
  rfl

theorem ArchLab.emb_flip (A : ArchLab D) (τ : D.what₂.Tau) :
    A.flip.emb τ = (starRingEnd ℂ).comp (A.emb τ) := by
  rcases A with ⟨p, s⟩
  cases s <;> ext x <;> simp [ArchLab.emb, ArchLab.flip]

theorem isLabOf_conj {σ : D.what₂.LL →+* ℂ} {A : ArchLab D} (h : IsLabOf σ A) :
    IsLabOf ((starRingEnd ℂ).comp σ) A.flip := by
  intro τ
  rw [labE_conj, h τ, ArchLab.emb_flip]

variable (D) in

def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A

variable (D) in

def LabUnique : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (A A' : ArchLab D), IsLabOf σ A → IsLabOf σ A' → A = A'

open Classical in

def labOf (σ : D.what₂.LL →+* ℂ) : ArchLab D :=
  if h : ∃ A : ArchLab D, IsLabOf σ A then h.choose else baseLab D

theorem labOf_spec {σ : D.what₂.LL →+* ℂ} (h : ∃ A : ArchLab D, IsLabOf σ A) : IsLabOf σ (labOf σ) := by
  unfold labOf
  rw [dif_pos h]
  exact h.choose_spec

theorem labOf_base (hU : LabUnique D) : labOf (D := D) D.what₂.embLL = baseLab D :=
  hU _ _ _ (labOf_spec ⟨_, isLabOf_base⟩) isLabOf_base

def rl (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : D.what₂.Tau → X := fun ρ => S (A.perm.symm ρ)

theorem rl_base {X : Type*} (S : D.what₂.Tau → X) : rl (baseLab D) S = S := rfl

theorem rl_flip (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : rl A.flip S = rl A S := rfl

theorem rl_pos (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : rl A.pos S = rl A S := rfl

def cv (σ : D.what₂.LL →+* ℂ) {X : Type*} (f : X → D.what₂.LL) : X → ℂ := fun x => σ (f x)

theorem cv_base {X : Type*} (f : X → D.what₂.LL) : cv D.what₂.embLL f = fun x => D.what₂.embLL (f x) := rfl

theorem cv_conj (σ : D.what₂.LL →+* ℂ) {X : Type*} (f : X → D.what₂.LL) :
    cv ((starRingEnd ℂ).comp σ) f = fun x => starRingEnd ℂ (cv σ f x) := rfl

def levSig (σ : D.what₂.LL →+* ℂ) {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E D.what₂.LL n) :
    Formalism.L2.DIV.LevDat D.host.E ℂ n where
  r := L.r
  hr := L.hr
  t := L.t
  s := L.s
  Pg := L.Pg
  Q := L.Q
  P := ⟨L.P.H, (Units.map σ.toMonoidHom).comp L.P.chi⟩
  cg := fun i PP => (Units.map σ.toMonoidHom).comp (L.cg i PP)
  xq := fun PP => (Units.map σ.toMonoidHom).comp (L.xq PP)

def eSig (σ : D.what₂.LL →+* ℂ) {G : Type*} (e : G →₀ D.what₂.LL) : G →₀ ℂ :=
  Finsupp.mapRange σ σ.map_zero e

def IsConjChar (σ : D.what₂.LL →+* ℂ) (χL : (AE D)ˣ →* D.what₂.LLˣ) (χ χσ : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D χσ ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 →
    ((χσ x : Circle) : ℂ) * D.what₂.embLL (χL x : D.what₂.LL) = ((χ x : Circle) : ℂ) * σ (χL x : D.what₂.LL)

theorem isConjChar_base {χL : (AE D)ˣ →* D.what₂.LLˣ} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) :
    IsConjChar D.what₂.embLL χL χ χ :=
  ⟨h, fun _ _ => rfl⟩

def IsThPKernelSig (ψ : AddChar (AF D.host.F) ℂ) (σ : D.what₂.LL →+* ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (j : ℕ) (Vj Wj : HSp D)
    (th : GA D Wj → GA D Vj → (Datum.WO Vj Wj → ℂ) → ℂ) : Prop :=
  ∃ (μσ : ℕ → (AE D)ˣ →* Circle) (ησ : (AE D)ˣ →* Circle),
    (∀ k, IsConjChar σ (μL k) (μ k) (μσ k)) ∧ IsConjChar σ ηL η ησ ∧
      Lift.IsThPKernel ψ μσ ησ j Vj Wj th

def IsStepKernelSig (ψ : AddChar (AF D.host.F) ℂ) (σ : D.what₂.LL →+* ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (j : ℕ) (V W : HSp D) (th : GA D V → GA D W → (Datum.WO V W → ℂ) → ℂ) : Prop :=
  ∃ (μσ : ℕ → (AE D)ˣ →* Circle) (ησ : (AE D)ˣ →* Circle),
    (∀ k, IsConjChar σ (μL k) (μ k) (μσ k)) ∧ IsConjChar σ ηL η ησ ∧
      Lift.IsStepKernel ψ μσ ησ j V W th

def IsChainKernelSig (ψ : AddChar (AF D.host.F) ℂ) (σ : D.what₂.LL →+* ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (m : ℕ) (Y : ℕ → HSp D)
    (th : ∀ k, GA D (Y k) → GA D (Y (k + 1)) → (Datum.WO (Y k) (Y (k + 1)) → ℂ) → ℂ) : Prop :=
  ∃ (μσ : ℕ → (AE D)ˣ →* Circle) (ησ : (AE D)ˣ →* Circle),
    (∀ k, IsConjChar σ (μL k) (μ k) (μσ k)) ∧ IsConjChar σ ηL η ησ ∧
      Lift.IsChainKernel ψ μσ ησ m Y th

theorem isThPKernelSig_base (ψ : AddChar (AF D.host.F) ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (hμ : ∀ k, IsHeckeChar D (μ k)) (hη : IsHeckeChar D η) (j : ℕ) (Vj Wj : HSp D)
    (th : GA D Wj → GA D Vj → (Datum.WO Vj Wj → ℂ) → ℂ) (h : Lift.IsThPKernel ψ μ η j Vj Wj th) :
    IsThPKernelSig ψ D.what₂.embLL μL ηL μ η j Vj Wj th :=
  ⟨μ, η, fun k => isConjChar_base (hμ k), isConjChar_base hη, h⟩

def deltaSig (A : ArchLab D) {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    MvPolynomial (Datum.FVar D m n) ℂ :=
  Datum.delta p q (rl A ap) (rl A am)

theorem deltaSig_base {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    deltaSig (m := m) (n := n) (baseLab D) p q ap am = Datum.delta p q ap am := rfl

def IsThetaPSig (ψ : AddChar (AF D.host.F) ℂ) (σ : D.what₂.LL →+* ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (j : ℕ) (Vj Wj : HSp D) {Sinf TK Tau : Type*} [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau] [MeasurableSpace (GA D Vj)]
    (ν : Measure (GA D Vj)) (𝓕 : Set (GA D Vj)) (pt : Sinf → (Datum.WO Vj Wj → ℂ))
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (GA D Vj → Tau))
    (thP : A →ₗ[ℂ] (TK →ₗ[ℂ] (GA D Wj → ℂ))) : Prop :=
  ∃ th, IsThPKernelSig ψ σ μL ηL μ η j Vj Wj th ∧ Lift.IsThetaP ν 𝓕 th pt io A thP

variable (D) in

def ConjCharUnique : Prop :=
  ∀ χ₁ χ₂ : (AE D)ˣ →* Circle, IsHeckeChar D χ₁ → IsHeckeChar D χ₂ →
    (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → χ₁ x = χ₂ x) → χ₁ = χ₂

end Formalism.IndefR.Conj

end
