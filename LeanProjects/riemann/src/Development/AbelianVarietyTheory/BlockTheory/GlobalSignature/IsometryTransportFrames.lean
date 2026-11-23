import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HasSig (W : HSpace E) (P Q : ℕ) : Prop := W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def withLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def frameMat (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e

def CarriesLat (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop := ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

example (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : (withLat W L hL hU).gram = W.gram := rfl

example (W : HSpace E) : withLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular = W := rfl

example (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) (x : W₁.V) :
    (frameMat W₁ W₂ e).mulVec (W₁.frame.repr x) = W₂.frame.repr (e x) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

end Spaces

def IsConjBy {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (T : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) : Prop :=
  ∀ h : HA (AF F) σ J₁,
    ((HA.mat (AF F) σ J₂ (φ h) : GL (Fin M₂) (AF F ⊗[F] E)) : Matrix (Fin M₂) (Fin M₂) (AF F ⊗[F] E)) *
        T.map (inclR (F := F) (AF F)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J₁ h : GL (Fin M₁) (AF F ⊗[F] E)) : Matrix (Fin M₁) (Fin M₁) (AF F ⊗[F] E))

def LatticeIndep (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSig W P Q →
    ∀ (L : Submodule (𝓞 D.host.E) W.V) (hL : Submodule.IsLattice D.host.E L)
      (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D W P Q μ ↔ IsVolMeas D (withLat W L hL hU) P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → CarriesLat W₁ W₂ e →
      ∃ φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjBy D.sp.cm.sig W₁.gram W₂.gram (frameMat W₁ W₂ e.toLinearMap) φ ∧
        (∀ h, h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram ↔
          φ h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram))
            (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram)),
          IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (φ '' 𝓕) (μ.map φ))

def VolEqOfIsometric (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D → ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → D.vol W₁ = D.vol W₂

def VolIndep (D : D7) : Prop := LatticeIndep D ∧ IsometryTransport D ∧ VolEqOfIsometric D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames
