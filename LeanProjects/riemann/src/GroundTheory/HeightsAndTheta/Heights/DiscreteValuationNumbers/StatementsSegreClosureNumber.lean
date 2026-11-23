import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreClosureNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) →
    ∀ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
      IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ →
      aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ As : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ,
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
    ∀ Cs : Fin (1 + n) → MvPolynomial (Fin (1 + n) ⊕ Fin (1 + n)) ℤ,
      IsPairExpansion (N - 1 + a + r) (zetaPowTimes n (N - 1 + a) R) Cs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        (-1) ^ a * pairNum (pointIdeal O (pairProjCoord y e φ φ' t))
          (Fin.append (fun _ : Fin 1 => zetaFirst a₀) (fun j => liftPairDeg (z j)))
          (Fin.append (fun _ : Fin 1 => zetaSecond a₀') (fun j => liftPairDeg (z' j)))
          (Fin.append (fun _ : Fin 1 => f₀) (fun j => liftPairForm M M' (fz j)))
          (Fin.append (fun _ : Fin 1 => g₀) (fun j => liftPairForm M M' (gz j))) Cs
          (Q.map liftPairDeg)

section Examples

def pointOne : (Σ k, PointIdx k) → LineFieldDyadic := fun _ => 1

instance pointPairIdx_unique : ∀ o, Unique (bundleIdx (bundleIdx PointIdx 1) 1 o)
  | none => inferInstanceAs (Unique (Fin 1))
  | some none => inferInstanceAs (Unique (Fin 1))
  | some (some _) => inferInstanceAs (Unique (Fin 1))

abbrev pointBundle {s : LineFieldDyadic} (hs : s ≠ 0) :
    ChartBundle ℤ_[2] (segreVec pointOne) 1 (Fin 1 → LineFieldDyadic) :=
  scaledTrivBundle ℤ_[2] (segreVec pointOne) 1 hs

def pointPhi : Fin 1 → Module.Dual LineFieldDyadic (Fin 1 → LineFieldDyadic) :=
  fun l => LinearMap.proj l

def pointPhi' : Fin 1 → Module.Dual LineFieldDyadic (Fin 1 → LineFieldDyadic) :=
  fun l => (algebraMap ℤ_[2] LineFieldDyadic ((2 : ℕ) : ℤ_[2]))⁻¹ • LinearMap.proj l

def pointPairCoord : (Σ o, bundleIdx (bundleIdx PointIdx 1) 1 o) → GenericCoordField 1 :=
  pairProjCoord pointOne (scaledBasis 1 (one_ne_zero (α := LineFieldDyadic))) pointPhi pointPhi'
    (genericCoords 1)

def dualGeneratorForm : MRing (bundleIdx (bundleIdx PointIdx 1) 1) ℤ_[2] := X ⟨some none, (0 : Fin 1)⟩

def scaledDualGeneratorForm : MRing (bundleIdx (bundleIdx PointIdx 1) 1) ℤ_[2] :=
  C ((2 : ℕ) : ℤ_[2]) * X ⟨none, (0 : Fin 1)⟩

theorem mem_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    f ∈ W ∧ W.IsPrime ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact ⟨hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)), hW.1.1.1, hW.2⟩
  · exact absurd rfl h

def pointExpansion : Fin (1 + 1) → MvPolynomial (Fin (1 + 1) ⊕ Fin (1 + 1)) ℤ :=
  fun i => if (i : ℕ) < 1 then 1 else 0

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
