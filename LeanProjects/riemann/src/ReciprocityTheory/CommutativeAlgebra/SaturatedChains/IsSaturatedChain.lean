import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA

universe u

def IsSaturatedChain {R : Type*} [CommRing R] (s : LTSeries (PrimeSpectrum R)) : Prop :=
  ∀ i : Fin s.length, s (Fin.castSucc i) ⋖ s (Fin.succ i)

def IsCatenary (R : Type*) [CommRing R] : Prop :=
  ∀ s s' : LTSeries (PrimeSpectrum R), s.head = s'.head → s.last = s'.last →
    IsSaturatedChain s → IsSaturatedChain s' → s.length = s'.length

def DimFormula (R : Type*) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = ringKrullDim R

def IsCMQuot (R : Type u) [CommRing R] : Prop :=
  ∃ (P : Type u) (_ : CommRing P) (_ : IsLocalRing P) (f : P →+* R),
    IsCM P ∧ Function.Surjective f

end ReciprocityTheory.CA
