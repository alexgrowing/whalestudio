import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OddWindowBounds

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions ReciprocityTheory.Gal

def eFactor {L : Type} [Field L] (q : ℕ) (s : ℤ) (Y : Lˣ) : L :=
  (1 - (Y : L) * (q : L) ^ (-s)) * (1 - ((Y⁻¹ : Lˣ) : L) * (q : L) ^ (-s)) +
    ((q : L) - 1) * (q : L) ^ (-(2 * s))

example : eFactor (L := ℚ) 3 1 1 = 2 / 3 := by
  norm_num [eFactor]

def bigN (R : Ranks) : ℕ := R.k + R.m * (R.t + (R.r + 6) + 1)

def UnramAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A' : Type} [Group A']
    (φ : G E Ω →* A') (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (X : NTw R H what₂ LL0 N)

def Admissible (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) : Prop :=
  ∀ P ∈ Q, IsSplitPl H P ∧ (∀ P', IsConjPl H P P' → P' ∈ Q) ∧
    P ∉ placesOver H.E (X.l i) ∧ UnramAt (X.lamG i lam) P

def evalTh (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) {L : Type} [Field L]
    (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ) : L :=
  ∑ x : X.RCG i Q, φ (X.th i Q lam x) * (ψ x : L)

def lamPsi (i : X.Tw) (lam : X.abelian₂ i) (Q : Finset (PlE H)) {L : Type} [Field L]
    (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ) : G H.E N.Om →* Lˣ :=
  ((Units.map (φ.comp (algebraMap (X.O i) (FractionRing (X.O i)))).toMonoidHom).comp
    (X.lamG i lam)) * ψ.comp (X.art i Q)

open Classical in

def RelAt (i : X.Tw) (lam : X.abelian₂ i) (s : ℤ) : Prop :=
  ∀ Q : Finset (PlE H), Admissible X i lam Q →
  ∀ P ∈ Q, ∀ P' : PlE H, IsConjPl H P P' →
  ∀ (L : Type) [Field L] (φ : FractionRing (X.O i) →+* L) (ψ : X.RCG i Q →* Lˣ),
    UnramAt (ψ.comp (X.art i Q)) P → UnramAt (ψ.comp (X.art i Q)) P' →
    ∃ ψ' : X.RCG i (Q \ {P, P'}) →* Lˣ,
      ψ'.comp (X.res i Q (Q \ {P, P'}) Finset.sdiff_subset) = ψ ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
      ∀ σ : G H.E N.Om, IsFrob (F := H.E) A (normV P) σ →
        evalTh X i lam Q φ ψ =
          eFactor (normV P) s (lamPsi X i lam Q φ ψ σ⁻¹) * evalTh X i lam (Q \ {P, P'}) φ ψ'

def DistRel : Prop :=
  ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ s : ℤ, X.s2 i lam = 2 * s ∧ 1 ≤ s ∧ s ≤ (bigN R : ℤ) + 1 ∧
    RelAt X i lam s

end Record

def ToricDistribution (D : D7) : Prop := DistRel D.ntw

end GlobalTheory.IndefiniteRowSideFullHecke.OddWindowBounds

end
