import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def IsClassTerm {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

theorem IsClassTerm.unique {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {c : Ideal (OF E)} {χ : HChar E} {y : (Af E)ˣ} {T T' : ℂ} (h : IsClassTerm φ s κ c χ y T) (h' : IsClassTerm φ s κ c χ y T') :
    T = T' := by
  obtain ⟨S, hS, rfl⟩ := h
  obtain ⟨S', hS', rfl⟩ := h'
  rw [hS.unique hS']

theorem isToricSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) :
    IsToricSum φ s κ c χ T ↔ Finite (PicO c) ∧ ∃ t : PicO c → ℂ, (∀ q, IsClassTerm φ s κ c χ q.out (t q)) ∧ T = ∑ᶠ q, t q := by
  refine and_congr_right fun _ => ⟨fun ⟨S, hS, hT⟩ => ⟨_, fun q => ⟨S q, hS q, rfl⟩, hT⟩, fun ⟨t, ht, hT⟩ => ?_⟩
  choose S hS hS' using ht
  exact ⟨S, hS, by rw [hT]; exact finsum_congr hS'⟩

def IsHostDatum {R : Ranks} (H : Host R) {I : Type} [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E))
    (χ : HChar H.E) : Prop :=
  IsCMType φ ∧ (∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) ∧ 1 ≤ s ∧ (∀ τ, 1 ≤ κ τ) ∧ IsBaseCond 𝔣 ∧ IsValChar φ s κ 𝔣 ∅ χ

def below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (OF E) :=
  P.under (OF E)

theorem over_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Over P (below P) := rfl

open Classical in

def belowSet {E : Type} [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (OF E)) :=
  Q.image below

theorem splits_below {R : Ranks} (H : Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : Splits (below P) := by
  obtain ⟨x, hx, hx'⟩ := h
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ a : 𝓞 H.E, ((c a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := fun a => rfl
  refine ⟨P, P.comap c.toRingHom c.surjective, fun e => ?_, rfl, ?_⟩
  · have : x ∈ (P.comap c.toRingHom c.surjective).asIdeal := e ▸ hx
    exact hx' (c x) (hc x) this
  · ext a
    have : c (algebraMap (OF H.E) (𝓞 H.E) a) = algebraMap (OF H.E) (𝓞 H.E) a := by
      apply RingOfIntegers.ext
      apply H.φ₀.injective
      show H.φ₀ (H.conj ((a : maximalRealSubfield H.E) : H.E)) = H.φ₀ ((a : maximalRealSubfield H.E) : H.E)
      rw [H.toHostAx.conjE_apply]
      exact (a : maximalRealSubfield H.E).2 H.φ₀
    show c (algebraMap (OF H.E) (𝓞 H.E) a) ∈ P.asIdeal ↔ algebraMap (OF H.E) (𝓞 H.E) a ∈ P.asIdeal
    rw [this]

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev Kbar (i : X.Tw) : Type := AlgebraicClosure (FractionRing (X.O i))

def toBar (i : X.Tw) : FractionRing (X.O0 i) →+* Kbar X i :=
  (algebraMap (FractionRing (X.O i)) (Kbar X i)).comp
    (IsFractionRing.lift (g := (algebraMap (X.O i) (FractionRing (X.O i))).comp (algebraMap (X.O0 i) (X.O i)))
      ((IsFractionRing.injective (X.O i) (FractionRing (X.O i))).comp (X.O_inj i)))

def IsRecMap (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) {c : Ideal (OF D.host.E)} (π : PicO c →* X.RCG i Q) : Prop :=
  ∀ P, P ∉ X.S0 i → P ∉ Q → ∀ σ : G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ →
    π (QuotientGroup.mk (unifAt P)) = (X.art i Q σ)⁻¹

def IsToricEltAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
    (u : Kbar X i),
    IsHostDatum D.host φ s κ 𝔣 χ ∧
    (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    (∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1) ∧
    u ≠ 0 ∧
    ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def atSide {i : X.Tw} (b : Bool) (ι : ℂ →+* Kbar X i) : ℂ →+* Kbar X i := if b then ι else ι.comp (starRingEnd ℂ)

def IsToricElt : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsToricEltAt X i (atSide X (X.sideL i lam) ι) lam s

variable {X}

theorem placesBelow_splitCoprimeConductor_of_admissible {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : BlochKatoReduction.Gen.QOk X i Q) {𝔣 : Ideal (OF D.host.E)}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) :
    IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q) ∧ ∀ q ∈ belowSet Q, ((X.l i : ℕ) : OF D.host.E) ∉ q.asIdeal := by
  classical
  constructor
  · intro q hq
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨splits_below D.host (hQ.1 P hP), fun h => Finset.disjoint_left.1 hQ.2.1 hP (h𝔣 P h)⟩
  · intro q hq h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.1 hQ.2.1 hP (X.twistExcludedPlaces_contains_residueChar i ?_)
    have : algebraMap (OF D.host.E) (𝓞 D.host.E) ((X.l i : ℕ) : OF D.host.E) ∈ P.asIdeal := h
    rwa [map_natCast] at this

end Record

end GlobalTheory.ToricDenom
