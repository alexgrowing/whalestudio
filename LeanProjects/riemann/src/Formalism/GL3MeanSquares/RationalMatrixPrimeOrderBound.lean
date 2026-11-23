import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.RamifiedHeckeModels

open Finset Matrix ComplexConjugate Formalism.HermitianLattices.LocalLatticeBases

def RationalMatrixPrimeOrderBound : Prop :=
  ∀ (n p : ℕ), p.Prime → ∀ A : Matrix (Fin n) (Fin n) ℚ, A ^ p = 1 → A ≠ 1 → p ≤ n + 1

def LogRatioAtMostOne : Prop := ∀ q : ℕ, 3 ≤ q → Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2) ≤ 1

def LemmaC_twist : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      (∀ s ∈ S, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R (S ⧸ (S.map ((ϖ ^ b) • U)).comap S.subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

def LemmaC_twist_ram : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

def TableauExponentRange : Prop :=
  ∀ (μ : YoungDiagram) (T : SemistandardYoungTableau μ) (j : ℕ),
    (μ.cells.filter (fun c => T c.1 c.2 = j)).card ≤ μ.rowLen 0

def ConjRatioPowUnitModulus : Prop :=
  ∀ (z : ℂ) (g : ℕ), z ≠ 0 →
    ‖(z / conj z) ^ g‖ = 1 ∧ ((Complex.normSq z : ℝ) : ℂ) ^ g * (z / conj z) ^ g = z ^ (2 * g)

def HeckeKernelPreservesRamified : Prop :=
  ∀ (q : ℕ) [NeZero q] (n n' : ℕ) (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ),
    (∀ f, ∑ c : (ZMod q)ˣ, ph ((c : ZMod q) • f) = 0) →
    ∀ fW : Fin n' → ZMod q, ∑ c : (ZMod q)ˣ, kerK w ph ((c : ZMod q) • fW) = 0

def LatticeColumnOperatorBound : Prop :=
  ∀ (O L : Type) [CommRing O] [Field L] [Algebra O L] (M : ℕ → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module L (M i)] [∀ i, Module O (M i)] [∀ i, IsScalarTower O L (M i)]
    (S : ∀ i, Submodule O (M i)) (U : ∀ j, Module.End L (M j)) (K : ∀ j, M j →ₗ[L] M (j + 1))
    (c : ℕ → Lˣ) (ϖ : O) (e1 : ℕ) (w : ℕ → ℕ),
    (∀ j, (U (j + 1)).comp (K j) = (c j : L) • (K j).comp (U j)) →
    (∀ j, ∀ s ∈ S j, ϖ ^ e1 • (U (j + 1)) (K j s) ∈ S (j + 1)) →
    (∀ j, ∃ r : O, algebraMap O L r = ((c j)⁻¹ : Lˣ) * algebraMap O L ϖ ^ w j) →
    ∀ m : ℕ, ∀ s ∈ S 0,
      ϖ ^ (m * e1 + ∑ j ∈ range m, (m - j) * w j) • chainK L M K m (((U 0) ^ m) s) ∈ S m

def CauchySchwarzUnitModulus : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y y' : V) (T : ℝ) (ε : ℂ), 0 < T →
    ‖y‖ ^ 2 = 1 / T → ‖y'‖ ^ 2 = 1 / T →
    (‖(T : ℂ) * inner ℂ y y'‖ ≤ 1) ∧
    ((ε = 1 ∨ ε = -1) → (T : ℂ) * inner ℂ y y' = ε → y' = ε • y)

def ImprimitiveOrbitCondition : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (f : Fin n → ZMod q) (e : Fin n → ℤ) (xz : Fin n → ℚ),
    (∑ j, f j * (e j : ZMod q)) = 1 →
    (∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
      (∑ j, xz j * l j) ∈ Set.range (Int.cast : ℤ → ℚ)) →
    (∃ z : ℤ, (q : ℚ) * ∑ j, xz j * e j = z ∧ (z : ZMod q) = 1) →
    (¬ ∀ j, xz j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ j, (q : ℚ) * xz j ∈ Set.range (Int.cast : ℤ → ℚ))

end Formalism.HermitianLattices.RamifiedHeckeModels
