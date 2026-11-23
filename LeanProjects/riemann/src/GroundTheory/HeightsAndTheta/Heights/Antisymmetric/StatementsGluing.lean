import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

section Lattices

variable {Ω : Type*} [Field Ω]

def locAtIntPrime (p : ℕ) (A : Subring Ω) : Subring Ω :=
  Subring.closure ((A : Set Ω) ∪ {u | ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ u = (s : Ω)⁻¹})

def invertNat (m : ℕ) (A : Subring Ω) : Subring Ω :=
  Subring.closure ((A : Set Ω) ∪ {((m : Ω))⁻¹})

end Lattices

def LatticeSpread.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι : Type) [Fintype ι] (x : ι → Ω) (c : ι) (p : Nat.Primes)
    (E : Type) [AddCommGroup E] [Module Ω E] [FiniteDimensional Ω E]
    (L : Submodule (locAtIntPrime (p : ℕ) (chartRing ℤ x c).toSubring) E),
    Module.Finite (locAtIntPrime (p : ℕ) (chartRing ℤ x c).toSubring) L →
    Module.Projective (locAtIntPrime (p : ℕ) (chartRing ℤ x c).toSubring) L →
    Submodule.span Ω (L : Set E) = ⊤ →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧
      ∃ L' : Submodule (invertNat m (chartRing ℤ x c).toSubring) E,
        Module.Finite (invertNat m (chartRing ℤ x c).toSubring) L' ∧
        Module.Projective (invertNat m (chartRing ℤ x c).toSubring) L' ∧
        Submodule.span (locAtIntPrime (p : ℕ) (chartRing ℤ x c).toSubring) (L' : Set E) = L

section Join

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

def joinPt (x : ι → Ω) (z : κ → Ω') : ι × κ → Ω' :=
  segreJoin (fun i => algebraMap Ω Ω' (x i)) z

def pullbackLat {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    AddSubgroup (Ω' ⊗[Ω] E) :=
  AddSubgroup.closure {w | ∃ a ∈ chartRing ℤ (joinPt x z) q, ∃ v ∈ B.lat q.1,
    w = a • ((1 : Ω') ⊗ₜ[Ω] v)}

end Join

def ChartBundlePullback.Statement : Prop :=
  ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → Ω) (z : κ → Ω') (r : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
    (B : ChartBundle ℤ x r E),
    ∃ B' : ChartBundle ℤ (joinPt x z) r (Ω' ⊗[Ω] E), ∀ q, B'.lat q = pullbackLat B z q

section AddBlock

universe u

def addBlockIdx {K : Type*} (ι : K → Type u) (κ : Type u) : Option K → Type u
  | none => κ
  | some k => ι k

instance addBlockIdx.fintype {K : Type*} (ι : K → Type u) [∀ k, Fintype (ι k)] (κ : Type u)
    [Fintype κ] : ∀ o, Fintype (addBlockIdx ι κ o)
  | none => ‹Fintype κ›
  | some k => (inferInstance : Fintype (ι k))

def addBlockPt {K : Type*} {ι : K → Type u} {κ : Type u} {Ω Ω' : Type*} [Field Ω] [Field Ω']
    [Algebra Ω Ω'] (y : (Σ k, ι k) → Ω) (z : κ → Ω') : (Σ o, addBlockIdx ι κ o) → Ω'
  | ⟨none, i⟩ => z i
  | ⟨some k, i⟩ => algebraMap Ω Ω' (y ⟨k, i⟩)

def addBlockDeg {K : Type*} (a : K → ℤ) : Option K → ℤ
  | none => 0
  | some k => a k

end AddBlock

def NefAddBlock.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (κ : Type) [Fintype κ]
    (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] (y : (Σ k, ι k) → Ω) (z : κ → Ω')
    (a : K → ℤ),
    NefOnFibres (mCoordIdeal y) a →
      NefOnFibres (mCoordIdeal (addBlockPt (Ω := Ω) (Ω' := Ω') y z)) (addBlockDeg a)

section Inhabitants

example : ChartBundle ℤ (![1, 2] : Fin 2 → ℚ) 1 ℚ := lineBundle ℤ _ 1

example : (Σ o, addBlockIdx (fun _ : Fin 1 => Fin 2) (Fin 2) o) → ℚ :=
  addBlockPt (Ω := ℚ) (Ω' := ℚ) (fun p : (Σ _ : Fin 1, Fin 2) => ((p.2 : ℕ) : ℚ) + 1)
    (fun i : Fin 2 => ((i : ℕ) : ℚ) + 1)

end Inhabitants

end GroundTheory.Heights₂.Heights
