import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def RootSys (l : ℕ) (ζ : ℕ → Ω) : Prop := ∀ n, IsPrimitiveRoot (ζ n) (l ^ n) ∧ ζ (n + 1) ^ l = ζ n

def cyclotomicUnit (l : ℕ) (r : ℕ) : (ZMod (l ^ r))ˣ :=
  ZMod.unitOfCoprime (1 + l) (Nat.Coprime.pow_right r (by simp))

def smoothedLayer {r : ℕ} (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l :=
  fun s x => z s x - ((1 + l : ℕ) : Qbar l) * z s (x * cyclotomicUnit l r)

def TendsChar (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (φ : DirichletCharacter (Qbar l) l) : Prop :=
  ∀ n : ℕ, ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ x : (ZMod (l ^ r))ˣ, Cg n (χ r x) (φ (((x : ZMod (l ^ r)).val : ℕ) : ZMod l))

def HTLawSys (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (ζ : ℕ → Ω) (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∀ m, m₀ ≤ m → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPres A c m Z (ζ m) P o ∧
    ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j (ζ m) P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j (ζ m)))

def PinChi (e : ℕ) (A : ValuationSubring Ω) (_W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω →* (Qbar l)ˣ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ ‖(ν σ : Qbar l)‖ = 1) ∧
  ∃ (φ : DirichletCharacter (Qbar l) l) (α κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (ζ : ℕ → Ω)
    (L : PowerSeries (Qbar l)) (m₀ c₁ n₀ : ℕ),
    TendsChar χ φ⁻¹ ∧ ‖α‖ = 1 ∧ κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧ RootSys l ζ ∧
    (∀ n, L.coeff n ∈ c.O) ∧
    HTLawSys A c (fun r => smoothedLayer (Z r)) j ζ m₀ c₁ (fun m ψ z =>
      v m * κ * α ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)) ∧
    ∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

example (j : Ω →+* Qbar l) (ζ : Ω) (hζ : ζ ≠ 0) (b : ℕ) : htv j ζ (fun _ : Unit => Polynomial.X) (fun _ => 1) b = 1 := by
  simp [htv, hζ]

example (r : ℕ) (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) :
    smoothedLayer (fun (_ : G ℚ Ω) (_ : (ZMod (l ^ r))ˣ) => (1 : Qbar l)) s x = -((l : ℕ) : Qbar l) := by
  simp [smoothedLayer]

end GlobalTheory.KZ

end
