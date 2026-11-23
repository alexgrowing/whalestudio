import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalRingCardinality.HostCls

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlacesEmbeddingType

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def typeSet {R : Ranks} (H : Host R) : Bool → Set (H.E →+* ℂ)
  | false => H.cmType
  | true => {φ | ComplexEmbedding.conjugate φ ∈ H.cmType}

section Types

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

def EmbType (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  (∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ (Br.cEw D.nbr i w hw x)) ∧
  ∃ φ ∈ typeSet D.host ep, ∀ (x : D.host.E) (y : D.what₂.LL),
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ (Br.cEw D.nbr i w hw x) → D.what₂.embLL y = φ x

def PlaceType (ep : Bool) : Prop :=
  Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) ∧
  ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbType D i w hw ep τ ∧ ¬ EmbType D i w hw (!ep) τ

def UnramPlace : Prop :=
  w.asIdeal.ramificationIdx ℤ = 1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)

end Types

def SplitRowPrime {R : Ranks} (H : Host R) (l : ℕ) : Prop :=
  5 ≤ l ∧ H.cls l = PrimeClass.splitK ∧ ∀ k, l ≠ H.g k

def IsTypeCol (D : D7) (i : D.nd.Loc) (ep : Bool) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    Prop :=
  ∀ w, w ∈ col ↔ ∃ hw : w ∈ placesOver D.host.E (D.nd.l i), PlaceType D i w hw ep

def SplitPlaces_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → ∀ ep : Bool,
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      UnramPlace D i w hw ∧
      ∃ (wc : HeightOneSpectrum (𝓞 D.host.E)) (hwc : wc ∈ placesOver D.host.E (D.nd.l i)),
        IsConjPl D.host w wc ∧ wc ≠ w ∧
        ((PlaceType D i w hw ep ∧ PlaceType D i wc hwc (!ep)) ∨
          (PlaceType D i w hw (!ep) ∧ PlaceType D i wc hwc ep))) ∧
    ∃ col : Finset (HeightOneSpectrum (𝓞 D.host.E)), IsTypeCol D i ep col ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ wc, IsConjPl D.host w wc → (w ∈ col ↔ wc ∉ col)

def PairCount_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → ∀ (ep : Bool)
    (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsTypeCol D i ep col →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), col.card * locDeg D.host.E w = D.R.f

def SplitPlacesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SplitPlaces_at (Fm.D x i)

def SplitPlaces (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => SplitPlacesF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlacesEmbeddingType

end
