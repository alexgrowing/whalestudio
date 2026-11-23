import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def withLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def HasSignatureEverywhere (W : HSpace E) (P Q : ℕ) : Prop :=
  W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsIsometry (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  HSpace.IsIsomEmb W₁ W₂ e.toLinearMap

def CarriesLattice (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

def frameMatrix (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e.toLinearMap

example (W : HSpace E) : withLattice W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular = W := rfl

example (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : (withLattice W L hL hU).gram = W.gram := rfl

example (W : HSpace E) : IsIsometry W W (LinearEquiv.refl E W.V) ∧ CarriesLattice W W (LinearEquiv.refl E W.V) ∧
    frameMatrix W W (LinearEquiv.refl E W.V) = 1 :=
  ⟨fun _ _ => rfl, fun _ => Iff.rfl, by simp [frameMatrix]⟩

end Spaces

def Intertwines {A : Type} [CommRing A] {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) A)
    (g₁ : Matrix (Fin M₁) (Fin M₁) A) (g₂ : Matrix (Fin M₂) (Fin M₂) A) : Prop :=
  g₂ * C = C * g₁

def pointMatrix {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (HA.mat R σ J h).val

def baseChange {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) E) : Matrix (Fin M₂) (Fin M₁) (R ⊗[F] E) :=
  C.map (inclR R)

def IsConjugationBy {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E)
    (C : Matrix (Fin M₂) (Fin M₁) E) (Φ : HA R σ J₁ → HA R σ J₂) : Prop :=
  ∀ h : HA R σ J₁, Intertwines (baseChange R C) (pointMatrix R σ J₁ h) (pointMatrix R σ J₂ (Φ h))

example {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsConjugationBy R σ J J 1 id := by
  intro h
  rw [Intertwines, baseChange, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.one_mul]
  rfl

def LatticeIndependence (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W P Q →
    ∀ (L L' : Submodule (𝓞 D.host.E) W.V)
      (hL : Submodule.IsLattice D.host.E L) (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L)
      (hL' : Submodule.IsLattice D.host.E L') (hU' : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L')
      (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D (withLattice W L hL hU) P Q μ ↔ IsVolMeas D (withLattice W L' hL' hU') P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e → CarriesLattice W₁ W₂ e →
      ∃ Φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjugationBy (AF D.host.F) D.sp.cm.sig W₁.gram W₂.gram (frameMatrix W₁ W₂ e) Φ ∧
        (∀ h : HA (AF D.host.F) D.sp.cm.sig W₁.gram,
          HA.mat (AF D.host.F) D.sp.cm.sig W₁.gram h ∈ HFin (AF D.host.F) D.sp.cm.sig W₁.gram ↔
            HA.mat (AF D.host.F) D.sp.cm.sig W₂.gram (Φ h) ∈ HFin (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram), IsVolMeas D W₁ P Q μ →
          ∀ 𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (Φ '' 𝓕) (μ.map Φ)

def VolumeInvariance (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D →
    ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
      (∃ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e) → D.vol W₁ = D.vol W₂

def VolumeIndependence (D : D7) : Prop :=
  LatticeIndependence D ∧ IsometryTransport D ∧ VolumeInvariance D

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
