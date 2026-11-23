import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ChartValueBoundRamified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io.toAlgebra
        (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
          nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
            ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

def RamifiedEigenLifts : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (c : (D.host.E →+* ℂ) → π) (s : (D.host.E →+* ℂ) → Bool),
        (∀ τ, c (ComplexEmbedding.conjugate τ) = c τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧
        ∃ (φ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.V) (ψ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.Fr),
          (∀ ℓ i, (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p)) : ℝ) : EReal) ≤ nval Tc.V e (ψ ℓ i)) ∧
          (∀ ℓ ℓ' : Lt1 (T.Q.Dw j), ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 →
            ∑ i, (algebraMap Tc.V Tc.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) *
              C.ch.uvec ℓ i = 0) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1)
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i))
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧
          TB.OppositePairVanishing Tc.Fr (fun ℓ : Lt1 (T.Q.Dw j) => c ℓ.1) (fun ℓ => s ℓ.1)
            (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap Tc.V Tc.Fr (φ ℓ i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i))
            (fun ℓ => (0, ψ ℓ))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
