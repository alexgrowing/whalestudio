import Mathlib

namespace UpperTheory.V.Pr

open IsLocalRing

noncomputable abbrev qdim {R : Type} [CommRing R] (I : Ideal R) : WithBot ℕ∞ := ringKrullDim (R ⧸ I)

def NicePrimeEx : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (ϖ : R), ϖ ∈ maximalIdeal R →
    ∀ (N : ℕ), 1 ≤ N → ∀ (ι : Type) [Finite ι] (a : ι → Ideal R), (∀ i, qdim (a i) < (N : ℕ)) →
    ∀ I : Ideal R, ((N + 1 : ℕ) : WithBot ℕ∞) ≤ qdim I →
    ∃ p : Ideal R, p.IsPrime ∧ I ≤ p ∧ qdim p = 1 ∧ ϖ ∈ p ∧ ∀ i, ¬ a i ≤ p

structure LocData (R : Type) [CommRing R] where
  D1 : ℕ
  TI : Set (PrimeSpectrum R)
  TE : Set (PrimeSpectrum R)
  Good : Set (PrimeSpectrum R)
  Nice : Set (PrimeSpectrum R)
  Thick : Set (PrimeSpectrum R)
  sharp : Ideal R

namespace LocData

variable {R : Type} [CommRing R] (L : LocData R)

def Comp (P : PrimeSpectrum R) : Prop := P.asIdeal ∈ L.sharp.minimalPrimes

def Adj (P Q : PrimeSpectrum R) : Prop :=
  L.Comp P ∧ L.Comp Q ∧ (L.D1 : WithBot ℕ∞) ≤ qdim (P.asIdeal ⊔ Q.asIdeal)

def Link (p q : PrimeSpectrum R) : Prop :=
  p ∈ L.Nice ∧ p ∈ L.TE ∧ q ∈ L.Nice ∧ q ∈ L.TE ∧ ∃ e ∈ L.Thick, L.Comp e ∧ e ≤ p ∧ e ≤ q

def P1 : Prop := ∀ p ∈ L.Nice, p ∈ L.TI → p ∈ L.Good → ∀ P ≤ p, P ∈ L.Good

def flipTwoThree : Prop := ∀ p ∈ L.Nice, p ∈ L.TE → ∀ q, Relation.ReflTransGen L.Link p q →
  (∃ P ≤ p, P ∈ L.TI ∧ P ∈ L.Good) → ∀ P' ≤ q, P' ∈ L.TI → P' ∈ L.Good

structure Ok : Prop where
  good_up : ∀ P Q, P ≤ Q → P ∈ L.Good → Q ∈ L.Good
  ti_down : ∀ P Q, P ≤ Q → Q ∈ L.TI → P ∈ L.TI
  nice_type : ∀ p ∈ L.Nice, p ∈ L.TI ∨ p ∈ L.TE
  nice_good : ∀ I ∈ L.Good, (L.D1 : WithBot ℕ∞) ≤ qdim I.asIdeal → ∃ p ∈ L.Nice, I ≤ p
  nice_thick : ∀ e ∈ L.Thick, L.Comp e → ∀ I, e ≤ I → (L.D1 : WithBot ℕ∞) ≤ qdim I.asIdeal →
    ∃ p ∈ L.Nice, p ∈ L.TE ∧ I ≤ p
  comp : ∀ P ∈ L.TI, P.asIdeal ∈ minimalPrimes R → L.Comp P
  chain : ∀ P Q, L.Comp P → L.Comp Q → Relation.ReflTransGen L.Adj P Q
  dich : ∀ P, L.Comp P → P ∈ L.TI ∨ P ∈ L.Thick
  p1 : L.P1
  p23 : L.flipTwoThree

def Concl : Prop := ∀ I ∈ L.Good, I ∈ L.TI → (L.D1 : WithBot ℕ∞) ≤ qdim I.asIdeal →
  ∀ P ∈ L.TI, P.asIdeal ∈ minimalPrimes R → P ∈ L.Good

end LocData

def LocProp : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (L : LocData R), L.Ok → L.Concl

structure GlobData (X : Type) where
  TI : Set X
  Good : Set X
  Core : Set X
  Cl : Set X
  EE : Set X

namespace GlobData

variable {X : Type} [TopologicalSpace X] (M : GlobData X)

def CompI (Y : Set X) : Prop := Y ∈ irreducibleComponents X ∧ (Y ∩ M.TI).Nonempty

structure Ok : Prop where
  cl_sub : M.Cl ⊆ M.Core
  conn : IsPreconnected M.Core
  jac : ∀ C, IsClosed C → (C ∩ M.Core).Nonempty → (C ∩ M.Cl).Nonempty
  dense : M.Core ⊆ closure (M.Cl \ M.EE)
  meets : ∀ Y, M.CompI Y → (Y ∩ M.Core).Nonempty
  loc : ∀ x ∈ M.Cl, ∀ Y Y', M.CompI Y → M.CompI Y' → x ∈ Y → x ∈ Y' → Y ⊆ M.Good → Y' ⊆ M.Good
  off : ∀ x ∈ M.Cl \ M.EE, ∃ Y, M.CompI Y ∧ x ∈ Y
  seed : ∃ Y, M.CompI Y ∧ Y ⊆ M.Good

end GlobData

def GlobProp : Prop := ∀ (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] (M : GlobData X),
  M.Ok → M.TI ⊆ M.Good

structure Chart {X : Type} [TopologicalSpace X] (x : X) {R : Type} [CommRing R] [IsLocalRing R]
    (f : PrimeSpectrum R → X) : Prop where
  cont : Continuous f
  pt : f (closedPoint R) = x
  min : ∀ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R → closure {f P} ∈ irreducibleComponents X
  onto : ∀ Y ∈ irreducibleComponents X, x ∈ Y → ∃ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R ∧ closure {f P} = Y

def ChartOfFlat : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (C : Type) [CommRing C] (j : PrimeSpectrum C → X), Topology.IsOpenEmbedding j →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [Algebra C R] [Module.Flat C R],
      Chart (j (PrimeSpectrum.comap (algebraMap C R) (closedPoint R))) (j ∘ PrimeSpectrum.comap (algebraMap C R))

def GlobOfCharts : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (M : GlobData X), IsOpen M.TI → IsClosed M.Good →
    ∀ (x : X) (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (f : PrimeSpectrum R → X), Chart x f →
    ∀ L : LocData R, L.TI = f ⁻¹' M.TI → L.Good = f ⁻¹' M.Good → L.Concl →
      ((∀ P ∈ minimalPrimes R, (L.D1 : WithBot ℕ∞) ≤ qdim P) →
        ∀ Y Y', M.CompI Y → M.CompI Y' → x ∈ Y → x ∈ Y' → Y ⊆ M.Good → Y' ⊆ M.Good) ∧
      ((∀ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R → P ∈ L.TI) → ∃ Y, M.CompI Y ∧ x ∈ Y) ∧
      ((∃ I ∈ L.Good, I ∈ L.TI ∧ (L.D1 : WithBot ℕ∞) ≤ qdim I.asIdeal) → ∃ Y, M.CompI Y ∧ Y ⊆ M.Good)

example : (⟨∅, ∅, ∅, ∅, ∅⟩ : GlobData PUnit).Cl ⊆ (⟨∅, ∅, ∅, ∅, ∅⟩ : GlobData PUnit).Core := subset_rfl

end UpperTheory.V.Pr
