import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.IdemDataBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ChartDirectionsEigen : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∀ (ℓ : Lt1 (T.Q.Dw j)) (a : 𝓞 D.host.E),
        (Matrix.of fun i m => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), m) 1) (C.ch.B.A.act a i)).mulVec
          (C.ch.uvec ℓ) = io (embK T.Q.c ℓ.1 a) • C.ch.uvec ℓ

def IntegralBiextension : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ B : Germ.FB Tc.V (chD C.ch) (𝓞 D.host.E), B.IsCanonGauge Tc.Fr C.ch.h ∧
        ∀ a i, B.actK Tc.Fr a i = C.ch.B.A.act a i

def PrimeConductorEigenLifts : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ φ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.V, ∀ ℓ ℓ' : Lt1 (T.Q.Dw j),
        ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 →
        ∑ i, (algebraMap Tc.V Tc.Fr (φ ℓ' i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0

namespace Pf.EigA

theorem idem_data {E : Type} [Field E] [NumberField E] {k V : Type} [Field k] [CommRing V] [Algebra V k]
    (ψ : E →+* k) (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (c : Fin n → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  obtain ⟨b, c, h1, h2⟩ := idem_data_basis ψ hint w hw
  set eq := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun i => b (eq.symm i), fun i => c (eq.symm i), ?_, fun a => ?_⟩
  · rw [Equiv.sum_comp eq.symm (fun x => algebraMap V k (c x) * ψ (algebraMap (𝓞 E) E (b x)))]
    exact h1
  · obtain ⟨m, hm1, hm2⟩ := h2 a
    refine ⟨fun i j => m (eq.symm i) (eq.symm j), fun i => ?_, fun j => ?_⟩
    · rw [hm1, ← Equiv.sum_comp eq.symm (fun x => m (eq.symm i) x • b x)]
    · rw [Equiv.sum_comp eq.symm (fun x => (m x (eq.symm j) : k) * algebraMap V k (c x))]
      exact hm2 _

end Pf.EigA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
