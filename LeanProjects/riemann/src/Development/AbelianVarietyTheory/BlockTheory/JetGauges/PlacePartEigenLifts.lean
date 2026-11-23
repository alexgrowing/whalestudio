import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections

section Types

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
variable (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F))

def placeOf (τ : E →+* ℂ) : Ideal (𝓞 E) :=
  la.asIdeal.comap (RingOfIntegers.mapRingHom (embF c τ))

def placePair (τ : E →+* ℂ) : Sym2 (Ideal (𝓞 E)) :=
  s(placeOf c la τ, placeOf c la (ComplexEmbedding.conjugate τ))

abbrev Pairs : Type := Set.range (placePair c la)

instance : Fintype (Pairs c la) := by classical exact Set.fintypeRange _

instance : DecidableEq (Pairs c la) := Classical.decEq _

def pairOf (τ : E →+* ℂ) : Pairs c la := ⟨placePair c la τ, τ, rfl⟩

def IsSide (s : (E →+* ℂ) → Bool) : Prop :=
  (∀ τ σ, placeOf c la τ = placeOf c la σ → s τ = s σ) ∧
    ∀ τ, s (ComplexEmbedding.conjugate τ) = !s τ

end Types

section Parts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

abbrev HK (C : IntegralChartA3 Xo c T io y) : Type := (Fin (chD C.ch) → T.Fr) × (Fin (chD C.ch) → T.Fr)

def actH (C : IntegralChartA3 Xo c T io y) (a : 𝓞 E) (ξ : HK C) : HK C :=
  letI := io.toAlgebra
  OactH T.Fr C.ch.B a ξ

def latH (C : IntegralChartA3 Xo c T io y) : Set (HK C) :=
  letI := io.toAlgebra
  Hset (R := T.V) T.Fr C.ch.h

def dir (C : IntegralChartA3 Xo c T io y) (ℓ : Lt1 Dw) : Fin (chD C.ch) → T.Fr :=
  letI := io.toAlgebra
  C.ch.uvec ℓ

def IsType (C : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ) (ξ : HK C) : Prop :=
  ∀ a : 𝓞 E, actH C a ξ = io (embK c τ a) • ξ

def IsTypeDecomp (C : IntegralChartA3 Xo c T io y) (ξ : HK C) (η : (E →+* ℂ) → HK C) : Prop :=
  (∀ σ, IsType C σ (η σ)) ∧ ∑ σ, η σ = ξ

def InPlacePart (la : HeightOneSpectrum (𝓞 c.F)) (C : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ) (ξ : HK C) : Prop :=
  ∃ η, IsTypeDecomp C ξ η ∧ ∀ σ, placeOf c la σ ≠ placeOf c la τ → η σ = 0

def IsLiftSystem (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ) (β : ℝ) (s : (E →+* ℂ) → Bool)
    (C : IntegralChartA3 Xo c T io y) (uh : Lt1 Dw → HK C) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr) : Prop :=
  (∀ ℓ, uh ℓ ∈ latH C) ∧
  (∀ ℓ, InPlacePart la C ℓ.1 (uh ℓ)) ∧
  (∀ ℓ, (uh ℓ).1 = dir C ℓ) ∧
  (∀ ℓ, ∃ η, IsTypeDecomp C (uh ℓ) η ∧ η ℓ.1 = uh ℓ + (0, ψ ℓ)) ∧
  (∀ ℓ, InPlacePart la C ℓ.1 (0, ψ ℓ)) ∧
  (∀ ℓ i, (((-β : ℝ)) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧
  (OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pairOf c la ℓ.1) (fun ℓ => s ℓ.1) uh uh) ∧
  (OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pairOf c la ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) uh) ∧
  (OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => pairOf c la ℓ.1) (fun ℓ => s ℓ.1) uh (fun ℓ => (0, ψ ℓ)))

def chartVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Germ.PS T.Fr n (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P

def IsIntHarm (Dw : Datum H) (T : CDVR) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr) : Prop :=
  P ∈ harmK Dw.mult n T.Fr ComplexEmbedding.conjugate (fun _ => True) (fun _ => 1) ∧
    ∀ m, P.coeff m ∈ (algebraMap T.V T.Fr).range

def minPairs (la : HeightOneSpectrum (𝓞 c.F)) (s : (E →+* ℂ) → Bool) {n : ℕ} (m : LtN Dw n →₀ ℕ) : ℕ :=
  pairMin (fun ℓ : LtN Dw n => pairOf c la ℓ.1) (fun ℓ => s ℓ.1) m

def NoMixedColumn (la : HeightOneSpectrum (𝓞 c.F)) {n : ℕ} (m : LtN Dw n →₀ ℕ) : Prop :=
  ∀ ℓ ∈ m.support, ∀ ℓ' ∈ m.support, ℓ.2.2 = ℓ'.2.2 →
    placeOf c la ℓ'.1 ≠ placeOf c la (ComplexEmbedding.conjugate ℓ.1)

end Parts

def vdAt (D : D7) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) : ℝ :=
  ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p

def EigenLifts : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      (∃ s, IsSide T.Q.c la s) ∧
      ∀ s, IsSide T.Q.c la s → ∃ uh ψ, IsLiftSystem la e (vdAt D la p) s C uh ψ

def ValueBound : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k n : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr),
      IsIntHarm (T.Q.Dw j) Tc P → ∀ f : Germ.PS Tc.Fr n (chD C.ch), IsIntPS Tc f →
      (∀ s, IsSide T.Q.c la s → ∀ M : ℕ, (∀ m ∈ P.support, minPairs la s m ≤ M) →
        ((-(vdAt D la p * (M : ℝ)) : ℝ) : EReal) ≤ nval Tc.V e (chartVal C k f P)) ∧
      ((-(vdAt D la p * (P.totalDegree : ℝ) / 2) : ℝ) : EReal) ≤ nval Tc.V e (chartVal C k f P) ∧
      ((∀ m ∈ P.support, NoMixedColumn la m) → 0 ≤ nval Tc.V e (chartVal C k f P))

def WeightBound : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Germ.PS Tc.Fr n (chD C.ch), IsIntPS Tc f →
        ((-(vdAt D la p * (Formalism.L2.Pj.DF (T.Q.Dw j) a : ℝ) / 2) : ℝ) : EReal) ≤ nval Tc.V e (chartVal C k f P)

def RamifiedChart : Prop := ValueBound ∧ WeightBound ∧ EigenLifts

end GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts
