import Formalism.LocalRingCardinality.DataParamsS
import Formalism.LocalRingCardinality.DataBu

open MeasureTheory Matrix Formalism.MainNotions.S

noncomputable section

namespace Formalism.BasicNotions

def cdScaleTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A =
        D.cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

def dsigTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ →
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d → d = D.dsig τ

def TwCoverPair (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥D.LL0),
    ((p : ℕ) : NumberField.RingOfIntegers ↥D.LL0) ∈ w.asIdeal →
    (∃ w' : D.what₂.places.Pl, D.what₂.muAt w' ≠ D.what₂.mu0 ∧
      ∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ 0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)) →
    ∃ i, D.ntw.l i = p ∧
      ((∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ∨
       (∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0b i (x : ↥D.LL0)))

theorem twCoverPair_of {D : Formalism.BasicNotions.D7} (h : NTw.CoverAtSplitPlaces D.ntw) : TwCoverPair D := fun p hp w hw hw' =>
  let ⟨i, hi, h1⟩ := h p hp w hw hw'
  ⟨i, hi, Or.inl h1⟩

structure Ties (D : D7) : Prop where
  cdScale_tie : cdScaleTie D
  dsig_tie : dsigTie D

  bu_def : Rows.BuDefQ D.what₂

  tw_cover : TwCoverPair D

  baseField_isGalois : IsGalois ℚ ↥D.LL0

  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π

def GoodFTAll (D : Formalism.BasicNotions.D7) : Prop := ∀ σ, D.nd.goodRow σ

end Formalism.BasicNotions

end
