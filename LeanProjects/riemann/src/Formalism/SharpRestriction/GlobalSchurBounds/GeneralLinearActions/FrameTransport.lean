import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

structure GaugeFam (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) where

  μ : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Measure (HA (AF F) σ J)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

def FrameRel {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E)
    (B : Matrix (Fin M) (Fin M') E) (g : HA (AF F) σ J) (g' : HA (AF F) σ J') : Prop :=
  ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      B.map (inclR (AF F)) =
    B.map (inclR (AF F)) *
      ((HA.mat (AF F) σ J' g' : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E))

namespace GaugeFam

variable (G : GaugeFam F E σ)

def IsHaar : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHaarH F E σ M J (G.μ M J)

def BasisInv : Prop :=
  ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
    J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) →
    AllSome (fun e : HA (AF F) σ J ≃* HA (AF F) σ J' =>
      ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) fun e =>
      (G.μ M J).map e = G.μ M J'

def StepCompat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    AllSome (IsCharAF F) fun ψ =>
    AllSome (IsXbetaMeasure F E σ (M + 1) J ψ β) fun νX =>
    AllSome (fun e : Hstab (AF F) σ J x ≃* HA (AF F) σ J' =>
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) fun e =>
      IsCompatible F E σ (M + 1) J x (G.μ (M + 1) J) ((G.μ M J').map e.symm) νX

def IsGauge : Prop := G.IsHaar ∧ G.BasisInv ∧ G.StepCompat

end GaugeFam

def FrameTransport (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
    ∀ μ'' : Measure (HA (AF F) σ J'), IsHaarH F E σ M J' μ'' →
      (μ''.map e.symm).IsHaarMeasure ∧
      ∀ 𝓕'', IsFDH F E σ M J' μ'' 𝓕'' →
        IsFundamentalDomain (HstabFin (AF F) σ J x) (e ⁻¹' 𝓕'') (μ''.map e.symm) ∧
        μ''.map e.symm (e ⁻¹' 𝓕'') = μ'' 𝓕''

def volHE (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ENNReal :=
  covolume (HFinIn (AF F) σ J) (HA (AF F) σ J) (G.μ M J)

def volH (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) : ℝ := (volHE G M J).toReal

theorem volHE_spec (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (h : ∃ 𝓕, IsFDH F E σ M J (G.μ M J) 𝓕) :
    ∃ 𝓕, IsFDH F E σ M J (G.μ M J) 𝓕 ∧ volHE G M J = G.μ M J 𝓕 := by
  have hf : HasFundamentalDomain (HFinIn (AF F) σ J) (HA (AF F) σ J) (G.μ M J) := ⟨h⟩
  refine ⟨hf.ExistsIsFundamentalDomain.choose, hf.ExistsIsFundamentalDomain.choose_spec, ?_⟩
  simp [volHE, covolume, hf]

theorem volHE_eq (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (c : ENNReal)
    (h : AllSome (IsFDH F E σ M J (G.μ M J)) fun 𝓕 => G.μ M J 𝓕 = c) : volHE G M J = c := by
  obtain ⟨𝓕, h1, h2⟩ := volHE_spec G M J h.1
  rw [h2, h.2 𝓕 h1]

end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
