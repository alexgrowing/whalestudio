import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalMajorantConvergence

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

def IsUnitaryRep {G : Type} [Group G] [TopologicalSpace G] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (π : G →* (X ≃ₗᵢ[ℂ] X)) : Prop := ∀ x : X, Continuous fun g => π g x

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
  (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
  (h : Q = dblGram finSumFinEquiv J) (ν : (R ⊗[F] E)ˣ →* ℝ≥0) (K : Subgroup (HA R σ Q))

def HeightConv (m : Measure (HA R σ J)) (s : ℝ) : Prop :=
  Integrable (fun g : HA R σ J =>
    (hgtH σ Q ν K (ioH R σ h (g, 1)) : ℝ) ^ (s + (n : ℝ) / 2)) m

def SectionConv (m : Measure (HA R σ J)) (Φ : HA R σ Q → ℂ) (s₀ : ℂ) (s : ℝ)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (π : HA R σ J →* (X ≃ₗᵢ[ℂ] X)) (x y : X) : Prop :=
  ZetaConvH σ h m (flatH σ Q ν K Φ s₀ (s : ℂ)) (coef (fun g v => π g v) x y)

def ConvAt : Prop := ∀ m : Measure (HA R σ J), m.IsHaarMeasure →
  (∀ s : ℝ, (n : ℝ) / 2 - 1 < s → HeightConv σ h ν K m s) ∧
  ∀ t : ℕ, (n : ℤ) - 2 < t → ∀ (μ : (R ⊗[F] E)ˣ →* Circle),
    ∀ Φ ∈ degPSH σ Q ν K μ ((t : ℂ) / 2),
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (π : HA R σ J →* (X ≃ₗᵢ[ℂ] X)), IsUnitaryRep π →
    ∀ x y : X, ∀ s ∈ Set.Ioo ((n : ℝ) / 2 - 1) ((t : ℝ) / 2), SectionConv σ h ν K m Φ ((t : ℂ) / 2) s π x y

variable {σ h ν K}

end Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

abbrev SplitsIn (v : HeightOneSpectrum (𝓞 F)) : Prop := Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v

def IsMajorantAt (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  ∃ ε : Fin n → Bool, cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def LocalConvergence : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
  ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (h : Q = dblGram finSumFinEquiv J),
    (∀ v : HeightOneSpectrum (𝓞 F), SplitsIn E v → ∀ K : Subgroup (GLoc σ Q v),
      IsOpen (K : Set (GLoc σ Q v)) →
      IsCompact (K : Set (GLoc σ Q v)) → HasIwasawa σ Q K →
      ConvAt σ h (absEv F E v) K) ∧
    (∀ v : HeightOneSpectrum (𝓞 F), SplitsIn E v → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L →
      IsSelfDualAt σ J L v → ConvAt σ h (absEv F E v) (KFin σ Q L v)) ∧
    ∀ (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)), IsMajorantAt σ J w b →
      ConvAt σ h (absEw F E w) (KArch σ Q w b)

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Record

example {G : Type} [Group G] [TopologicalSpace G] : IsUnitaryRep (1 : G →* (ℂ ≃ₗᵢ[ℂ] ℂ)) := fun _ => continuous_const

example (σ : E →ₐ[F] E) {n : ℕ} (w : InfinitePlace F) :
    IsMajorantAt σ (1 : Matrix (Fin n) (Fin n) E) w (bc (compInf F E w) 1) := isMajorantFrame_one w

end GlobalTheory.IndefiniteRowSideFullHecke.LocalMajorantConvergence

end
