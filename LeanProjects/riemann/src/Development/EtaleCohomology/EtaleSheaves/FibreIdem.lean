import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
