import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlaceAnyLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

def harmVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (C : IntegralChartA3 Xo c Tc io yI) (k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) Tc.Fr)
    (f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)) : Tc.Fr :=
  letI := io.toAlgebra
  ∑ mo ∈ P.support, P.coeff mo *
    ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)

def GoodPlaceAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l₂ : Level T.Q.H) (Xo₂ : Moduli (T.Q.Dw j) l₂) (c₂ : Coeff l₂)
      (Tc : CDVR) (io : c₂.F →+* Tc.Fr) (yI : IntFr Xo₂ c₂ Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 c₂.F)), OverLa la Tc.V io e → yI.IsAlg →
      (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 c₂.F) ∉ la.asIdeal)) →
      ∀ (C : IntegralChartA3 Xo₂ c₂ Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
        (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
        ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
          0 ≤ nval Tc.V e (harmVal C k P f)

def RamPlaceAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l₂ : Level T.Q.H) (Xo₂ : Moduli (T.Q.Dw j) l₂) (c₂ : Coeff l₂)
      (Tc : CDVR) (io : c₂.F →+* Tc.Fr) (yI : IntFr Xo₂ c₂ Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 c₂.F)), OverLa la Tc.V io e → yI.IsAlg →
      ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 c₂.F) ∈ la.asIdeal) →
      ∀ (C : IntegralChartA3 Xo₂ c₂ Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
        (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
        ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
          (((-(((vLa la (p : c₂.F) : ℤ) : ℝ) * D.host.vdH p * (Formalism.L2.Pj.DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
            nval Tc.V e (harmVal C k P f)

theorem GoodPlaceAnyLevel.base (hG : GoodPlaceAnyLevel) :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
        (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
        ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
          0 ≤ nval Tc.V e (harmVal C k P f) :=
  fun D T h j hj _ hs => hG D T h j hj hs T.Q.l (T.Q.Xo j) T.Q.c

theorem RamPlaceAnyLevel.base (hG : RamPlaceAnyLevel) :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
        (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
        ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
          (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * D.host.vdH p * (Formalism.L2.Pj.DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
            nval Tc.V e (harmVal C k P f) :=
  fun D T h j hj _ hs => hG D T h j hj hs T.Q.l (T.Q.Xo j) T.Q.c

theorem GoodPlaceAnyLevel.cover (hG : GoodPlaceAnyLevel) (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    [StarRing (𝓞 D.host.E)] (hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a)
    (l₂ : Level T.Q.H) (Xo₂ : Moduli (T.Q.Dw j) l₂) (c₂ : Coeff l₂) (hF : c₂.F = T.Q.c.F)
    (Tc : CDVR) (io : c₂.F →+* Tc.Fr) (yI : IntFr Xo₂ c₂ Tc io) (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (ho : OverLa la Tc.V (io.comp (IntermediateField.equivOfEq hF.symm : T.Q.c.F →+* c₂.F)) e) (hy : yI.IsAlg)
    (hp : ∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal))
    (C : IntegralChartA3 Xo₂ c₂ Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr) (hP : P ∈ FFV (Dw := T.Q.Dw j) Tc a n)
    (f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)) (hf : ∀ b, IsIntPS Tc (f b)) :
    0 ≤ nval Tc.V e (harmVal C k P f) := by
  obtain ⟨F, fin, conj, zm, le⟩ := c₂
  dsimp only at hF
  subst hF
  exact hG D T h j hj hs l₂ Xo₂ _ Tc io yI e la ho hy hp C k a n P hP f hf

theorem RamPlaceAnyLevel.cover (hG : RamPlaceAnyLevel) (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    [StarRing (𝓞 D.host.E)] (hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a)
    (l₂ : Level T.Q.H) (Xo₂ : Moduli (T.Q.Dw j) l₂) (c₂ : Coeff l₂) (hF : c₂.F = T.Q.c.F)
    (Tc : CDVR) (io : c₂.F →+* Tc.Fr) (yI : IntFr Xo₂ c₂ Tc io) (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (ho : OverLa la Tc.V (io.comp (IntermediateField.equivOfEq hF.symm : T.Q.c.F →+* c₂.F)) e) (hy : yI.IsAlg)
    (p : ℕ) (hp : p ∈ D.host.condN.primeFactors) (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal)
    (C : IntegralChartA3 Xo₂ c₂ Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr) (hP : P ∈ FFV (Dw := T.Q.Dw j) Tc a n)
    (f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)) (hf : ∀ b, IsIntPS Tc (f b)) :
    (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * D.host.vdH p * (Formalism.L2.Pj.DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
      nval Tc.V e (harmVal C k P f) := by
  obtain ⟨F, fin, conj, zm, le⟩ := c₂
  dsimp only at hF
  subst hF
  exact hG D T h j hj hs l₂ Xo₂ _ Tc io yI e la ho hy p hp hpl C k a n P hP f hf

def ChartValAnyLevel : Prop := GoodPlaceAnyLevel ∧ RamPlaceAnyLevel

end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlaceAnyLevel
