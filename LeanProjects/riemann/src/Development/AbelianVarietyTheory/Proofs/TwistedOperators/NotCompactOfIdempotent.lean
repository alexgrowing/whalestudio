import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

def krylov {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A)
    (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ v) i

section Objects

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def tConj (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) : P ⊗[F] E →ₐ[F] P ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F P) σ

def tConj3 (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] : P ⊗[F] (E ⊗[F] R) →ₐ[F] P ⊗[F] (E ⊗[F] R) :=
  Algebra.TensorProduct.map (AlgHom.id F P) (Algebra.TensorProduct.map σ (AlgHom.id F R))

def PointsClause (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    Function.Injective (toMat σ J (γ : Matrix n n E) R) ∧
    (∀ u, toMat σ J (γ : Matrix n n E) R (lConj σ J (γ : Matrix n n E) R u) =
      adj (sigR σ R) (J.map (inclE (F := F) R)) (toMat σ J (γ : Matrix n n E) R u)) ∧
    ∀ g : GL n (E ⊗[F] R), g ∈ centPts σ J γ R ↔
      ∃ u ∈ normOne σ J (γ : Matrix n n E) R,
        toMat σ J (γ : Matrix n n E) R (u : LPts σ J (γ : Matrix n n E) R) =
          (g : Matrix n n (E ⊗[F] R))

def IsIdemFamily (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) {ι : Type}
    (ε : ι → Matrix n n E) : Prop :=
  (∀ i, ε i ∈ genAlg (γ : Matrix n n E)) ∧ (∀ i, ε i ≠ 0) ∧ (∀ i, ε i * ε i = ε i) ∧
    (∀ i j, i ≠ j → ε i * ε j = 0) ∧ ∀ i j, ε i * adj (σ : E →+* E) J (ε j) = 0

end Objects

def UnitBounded (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B]
    (τ : B →ₐ[F] B) : Prop :=
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  ∃ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D ∧
    ∀ u : B ⊗[F] AdeleRing (𝓞 F) F, u * sigR τ (AdeleRing (𝓞 F) F) u = 1 →
      ∃ β : B, IsUnit β ∧ u * inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D

def NormBounded (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B]
    (τ : B →ₐ[F] B) : Prop :=
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  ∃ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D ∧
    ∀ u : B ⊗[F] AdeleRing (𝓞 F) F, u * sigR τ (AdeleRing (𝓞 F) F) u = 1 →
      ∃ β : B, β * τ β = 1 ∧ u * inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D

def MatBounded {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  ∃ D : Set (Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)), IsCompact D ∧
    ∀ g ∈ centPts σ J γ (AdeleRing (𝓞 F) F), ∃ δ ∈ centRat σ J γ,
      (g : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) *
        (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) ∈ D

def CyclicField : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n K),
    M.charpoly.Separable → ∃ v, IsUnit (krylov M v).det

def CyclicSemilocal : Prop :=
  ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : Type) [Fintype n] [DecidableEq n]
    (M : Matrix n n A), M.charpoly.Separable → ∃ v, IsUnit (krylov M v).det

def CyclicAlgebra : Prop :=
  ∀ (A : Type) [CommRing A] (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A),
    IsUnit (krylov M v).det →
      (∃ e : AdjoinRoot M.charpoly ≃ₐ[A] genAlg M, e (AdjoinRoot.root _) = gen M) ∧
      Nonempty (Module.Basis n A (genAlg M)) ∧
      Function.Bijective (fun l : genAlg M => (l : Matrix n n A) *ᵥ v)

def PlusTensorBijective : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → Function.Bijective (plusTensor σ J (γ : Matrix n n E))

def PlusEtale : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → Function.Bijective (plusTensor σ J (γ : Matrix n n E)) → ClausePlus σ J γ

def PointsCommutant : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → ∀ (R : Type) [CommRing R] [Algebra F R],
      Function.Injective (toMat σ J (γ : Matrix n n E) R) ∧
      ∀ N : Matrix n n (E ⊗[F] R),
        N * (γ : Matrix n n E).map (inclE (F := F) R) =
          (γ : Matrix n n E).map (inclE (F := F) R) * N ↔
        ∃ u, toMat σ J (γ : Matrix n n E) R u = N

def PointsAdjoint : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ∀ (R : Type) [CommRing R] [Algebra F R] (u : LPts σ J (γ : Matrix n n E) R),
      toMat σ J (γ : Matrix n n E) R (lConj σ J (γ : Matrix n n E) R u) =
        adj (sigR σ R) (J.map (inclE (F := F) R)) (toMat σ J (γ : Matrix n n E) R u)

def PointsCentraliser : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → PointsClause σ J γ

def SplitClosed : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P] (n : Type) [Fintype n],
    Algebra.Etale F P → Nonempty (Module.Basis n F P) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω],
      ∃ φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω),
        (∀ ω : Ω, φ (1 ⊗ₜ (1 ⊗ₜ ω)) = fun _ => (ω, ω)) ∧
        ∀ u i, φ (tConj3 P σ Ω u) i = (φ u i).swap

def SplitIdempotents : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      ∃ ε : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P ⊗[F] E,
        (∀ i, ε i ≠ 0) ∧ (∀ i, ε i * ε i = ε i) ∧ (∀ i j, i ≠ j → ε i * ε j = 0) ∧
          ∀ i j, ε i * tConj P σ (ε j) = 0

def SubtorusOfIdempotents : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ∀ (s : ℕ) (ε : Fin s → Matrix n n E), IsIdemFamily σ J γ ε →
      ∃ A : SplitSubtorus σ J γ s, ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin s → Rˣ)
        (i : Fin s), (A.hom R t : Matrix n n (E ⊗[F] R)) * (ε i).map (inclE (F := F) R) =
          ((1 : E) ⊗ₜ[F] (t i : R)) • (ε i).map (inclE (F := F) R)

def SubtorusLaurent : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E)
    (s : ℕ) (A : SplitSubtorus σ J γ s),
    ∃ (S : Finset (Fin s → ℤ)) (C : (Fin s → ℤ) → Matrix n n (E ⊗[F] F)), ∀ t : Fin s → Fˣ,
      (A.hom F t : Matrix n n (E ⊗[F] F)) = ∑ a ∈ S, ((∏ j, t j ^ a j : Fˣ) : F) • C a

def CharacterMonomial : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (f : (Fin s → Fˣ) →* Ω)
    (S : Finset (Fin s → ℤ)) (c : (Fin s → ℤ) → Ω),
    (∀ t, f t = ∑ a ∈ S, ((∏ j, t j ^ a j : Fˣ) : F) • c a) →
      ∃ a : Fin s → ℤ, ∀ t, f t = algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)

def SeparatingPoints : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P] [Module.Finite F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      ∃ ψ : Fin k → (P ⊗[F] (E ⊗[F] F) →ₐ[F] AlgebraicClosure F),
        (∀ x, (∀ i, ψ i x = 0 ∧ ψ i (tConj3 P σ F x) = 0) → x = 0) ∧
        ∀ i, IsField (K i ⊗[F] E) → ∀ x, ψ i x = 0 → ψ i (tConj3 P σ F x) = 0

def SplitRankUpper : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClausePlus σ J γ → PointsClause σ J γ →
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i) →
      ∀ s : ℕ, Nonempty (SplitSubtorus σ J γ s) →
        s ≤ Nat.card {i : Fin k // ¬ IsField (K i ⊗[F] E)}

def TensorFieldIff : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E] [Nontrivial E]
    (P : Type) [CommRing P] [Algebra F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      (IsField (P ⊗[F] E) ↔ k = 1 ∧ ∀ i, IsField (K i ⊗[F] E))

def UnitaryCommutant : Prop :=
  ∀ (A : Type) [CommRing A] [CharZero A], IsField A → ∀ (σ : A →+* A), (∀ x, σ (σ x) = x) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A), IsHerm σ J → IsUnit J.det →
    ∀ a : Matrix n n A, (∀ g ∈ UJ σ J, (g : Matrix n n A) * a = a * (g : Matrix n n A)) →
      ∃ c : A, a = c • (1 : Matrix n n A)

def SubtorusNotCentral : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    IsField E → ∀ (s : ℕ), 1 ≤ s → ∀ A : SplitSubtorus σ J γ s,
      ∃ g ∈ UPts σ J F, ∃ t : Fin s → Fˣ, g * A.hom F t ≠ A.hom F t * g

def TracePerfect : Prop :=
  ∀ (F E L : Type) [Field F] [CharZero F] [CommRing E] [CommRing L] [Algebra F E] [Algebra E L]
    [Algebra F L] [IsScalarTower F E L] [Module.Finite F E] [Module.Free E L] [Module.Finite E L]
    [IsReduced L],
    Function.Bijective (fun x : L => (Algebra.traceForm E L x : L →ₗ[E] E))

def TraceClause : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClauseTrace σ J γ

def NormOnePacking : Prop :=
  ∀ (X : Type) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] [LocallyCompactSpace X]
    [T2Space X] [SecondCountableTopology X] [NoncompactSpace X] (τ : X →+* X), Continuous τ →
    (∀ x, τ (τ x) = x) → ∀ Λ : AddSubgroup X, Countable Λ →
    (∃ C : Set X, IsCompact C ∧ ∀ x, ∃ l ∈ Λ, x - l ∈ C) →
      ∃ D : Set X, IsCompact D ∧ ∀ u : X, u * τ u = 1 → ∃ β ∈ Λ, β ≠ 0 ∧ u * β ∈ D

def TensorLattice : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B],
    letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
      Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
    IsTopologicalRing (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    LocallyCompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    T2Space (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    SecondCountableTopology (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    Function.Injective (inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)) ∧
    (∀ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D →
      {β : B | inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D}.Finite) ∧
    ∃ C : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ x, ∃ β : B, x - inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ C

def FieldUnitBounded : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B]
    (τ : B →ₐ[F] B), IsField B → (∀ x, τ (τ x) = x) → UnitBounded F B τ

def NormOfUnitBounded : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B]
    (τ : B →ₐ[F] B), UnitBounded F B τ → NormBounded F B τ

def ProductUnitBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E] [Module.Finite F E]
    (σ : E →ₐ[F] E) (P : Type) [CommRing P] [Algebra F P] [Module.Finite F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      (∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ)) → UnitBounded F (P ⊗[F] E) (tConj P σ)

def MatOfNormBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → PointsClause σ J γ →
    NormBounded F (plusAlg σ J (γ : Matrix n n E) ⊗[F] E)
      (tConj (plusAlg σ J (γ : Matrix n n E)) σ) → MatBounded σ J γ

def CompactOfMatBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    MatBounded σ J γ → AdelicCompact σ J γ

def IdempotentDet : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E] [Module.Finite F E]
    (n : Type) [Fintype n] [DecidableEq n] (ε : Matrix n n E), ε ≠ 0 → ε * ε = ε →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R],
    letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
    ∃ (d : ℕ) (χ : Matrix n n (E ⊗[F] R) → R), 0 < d ∧ Continuous χ ∧ χ 1 = 1 ∧
      (∀ g h, h * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * h →
        χ (g * h) = χ g * χ h) ∧
      (∀ g : Matrix n n E, ∃ c : F, χ (g.map (inclE (F := F) R)) = algebraMap F R c) ∧
      ∀ g (t : R), g * ε.map (inclE (F := F) R) =
        ((1 : E) ⊗ₜ[F] t) • ε.map (inclE (F := F) R) → χ g = t ^ d

def NotCompactOfIdempotent : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ∀ ε ∈ genAlg (γ : Matrix n n E), ε ≠ 0 → ε * ε = ε →
    (∀ t : (AdeleRing (𝓞 F) F)ˣ, ∃ g ∈ centPts σ J γ (AdeleRing (𝓞 F) F),
      (g : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) * ε.map (inclE (F := F) (AdeleRing (𝓞 F) F)) =
        ((1 : E) ⊗ₜ[F] (t : AdeleRing (𝓞 F) F)) • ε.map (inclE (F := F) (AdeleRing (𝓞 F) F))) →
    ¬ AdelicCompact σ J γ

section Adjoint

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.cT_add (σ : A →+* A) (a b : Matrix n n A) :
    _root_.Formalism.UG.cT σ (a + b) = _root_.Formalism.UG.cT σ a + _root_.Formalism.UG.cT σ b := by
  ext i j
  simp [_root_.Formalism.UG.cT]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.cT_smul (σ : A →+* A) (c : A) (a : Matrix n n A) :
    _root_.Formalism.UG.cT σ (c • a) = σ c • _root_.Formalism.UG.cT σ a := by
  ext i j
  simp [_root_.Formalism.UG.cT]

theorem cT_cT (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (a : Matrix n n A) : cT σ (cT σ a) = a := by
  ext i j; simp [cT, hσ]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_add (σ : A →+* A) (J a b : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (a + b) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a + _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J b := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.GlobalTheory.RegSS.cT_add, Matrix.mul_add, Matrix.add_mul]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_smul (σ : A →+* A) (J : Matrix n n A) (c : A) (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (c • a) = σ c • _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.GlobalTheory.RegSS.cT_smul, Matrix.mul_smul,
    Matrix.smul_mul]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_zero (σ : A →+* A) (J : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J 0 = 0 := by
  have h : _root_.Formalism.UG.cT σ (0 : Matrix n n A) = 0 := by
    ext i j
    simp [_root_.Formalism.UG.cT]
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, h]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_one (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J 1 = 1 := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.Formalism.UG.cT_one, Matrix.nonsing_inv_mul _ hJ]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_mul (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a b : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (a * b) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J b * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.Formalism.UG.cT_mul]
  rw [show J⁻¹ * _root_.Formalism.UG.cT σ b * J * (J⁻¹ * _root_.Formalism.UG.cT σ a * J) =
      J⁻¹ * _root_.Formalism.UG.cT σ b * (J * J⁻¹) * _root_.Formalism.UG.cT σ a * J by simp only [Matrix.mul_assoc],
    Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_adj (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x)
    {J : Matrix n n A} (hH : _root_.Formalism.UG.IsHerm σ J) (hJ : IsUnit J.det) (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a) = a := by
  have hc : ∀ M : Matrix n n A, _root_.Formalism.UG.cT σ (_root_.Formalism.UG.cT σ M) = M := by
    intro M
    ext i j
    simp [_root_.Formalism.UG.cT, hσ]
  have hH' : _root_.Formalism.UG.cT σ J = J := hH
  have hJi : _root_.Formalism.UG.cT σ J⁻¹ = J⁻¹ := by
    have hl : _root_.Formalism.UG.cT σ J⁻¹ * J = 1 := by
      calc _root_.Formalism.UG.cT σ J⁻¹ * J = _root_.Formalism.UG.cT σ J⁻¹ * _root_.Formalism.UG.cT σ J := by rw [hH']
        _ = _root_.Formalism.UG.cT σ (J * J⁻¹) := (_root_.Formalism.UG.cT_mul σ J J⁻¹).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hJ, _root_.Formalism.UG.cT_one]
    exact (Matrix.inv_eq_left_inv hl).symm
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, _root_.Formalism.UG.cT_mul, hc, hJi, hH']
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ,
    Matrix.mul_one]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_algebraMap (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (e : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (algebraMap A (Matrix n n A) e) =
      algebraMap A (Matrix n n A) (σ e) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    _root_.GlobalTheory.RegSS.adj_smul, _root_.GlobalTheory.RegSS.adj_one σ hJ]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.isUnit_det_map {B : Type} [CommRing B] (f : A →+* B)
    {J : Matrix n n A} (hJ : IsUnit J.det) : IsUnit (J.map f).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hJ.map f

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_map {B : Type} [CommRing B] (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ x, f (σ x) = τ (f x)) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj τ (J.map f) (a.map f) = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a).map f := by
  have hcT : _root_.Formalism.UG.cT τ (a.map f) = (_root_.Formalism.UG.cT σ a).map f := by
    ext i j
    simp [_root_.Formalism.UG.cT, hf]
  have hinv : (J.map f)⁻¹ = J⁻¹.map f := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ, Matrix.map_one f f.map_zero f.map_one]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj, hcT, hinv, Matrix.map_mul]

theorem mem_UJ_iff_adj_mul (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ UJ σ J ↔ adj σ J (g : Matrix n n A) * (g : Matrix n n A) = 1 := by
  change cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J ↔ _
  rw [(adj_eq_iff σ hJ (g : Matrix n n A) _).1 rfl, Matrix.mul_assoc]
  constructor
  · intro h
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).mul_left_cancel (by rw [h, mul_one])
  · intro h; rw [h, Matrix.mul_one]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.mem_UJ_iff_mul_adj (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) (g : GL n A) :
    g ∈ _root_.Formalism.UG.UJ σ J ↔ (g : Matrix n n A) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = 1 := by
  change _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J ↔ _
  rw [mul_eq_one_comm]
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj]
  constructor
  · intro hg
    rw [show J⁻¹ * _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) =
        J⁻¹ * (_root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) by
      simp only [Matrix.mul_assoc], hg, Matrix.nonsing_inv_mul _ hJ]
  · intro hg
    calc _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)
        = J * (J⁻¹ * _root_.Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hJ]
      _ = J := by rw [hg, Matrix.mul_one]

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.adj_eq_inv (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) {g : GL n A} (hg : g ∈ _root_.Formalism.UG.UJ σ J) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A) :=
  (Units.inv_eq_of_mul_eq_one_right
    ((_root_.GlobalTheory.RegSS.mem_UJ_iff_mul_adj σ hJ g).1 hg)).symm

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.RegSS.commute_of_mem_genAlg {M N l : Matrix n n A} (h : N * M = M * N)
    (hl : l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M) : N * l = l * N := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg at hl
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hl h).eq

open Matrix NumberField in
open scoped TensorProduct in
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.RegSS.mem_genAlg_of_commute {M N : Matrix n n A} {v : n → A}
    (hv : Function.Bijective (fun l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M => (l : Matrix n n A) *ᵥ v))
    (h : N * M = M * N) : N ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M := by
  obtain ⟨l, hl⟩ := hv.2 (N *ᵥ v)
  have hlM : (l : Matrix n n A) * M = M * l :=
    (_root_.GlobalTheory.RegSS.commute_of_mem_genAlg (M := M) (N := M) rfl l.2).symm
  have key : N = l := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨l', rfl⟩ := hv.2 w
    have hll' : (l : Matrix n n A) * l' = l' * l :=
      _root_.GlobalTheory.RegSS.commute_of_mem_genAlg hlM l'.2
    have hNl' : N * (l' : Matrix n n A) = l' * N :=
      _root_.GlobalTheory.RegSS.commute_of_mem_genAlg h l'.2
    simp only [Matrix.toLin'_apply]
    simp only at hl
    rw [Matrix.mulVec_mulVec, hNl', ← Matrix.mulVec_mulVec, ← hl, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hll']
  exact key ▸ l.2

end Adjoint

section Quad

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.RegSS.quad_finite
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [h.finrank_eq]; norm_num)

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.RegSS.quad_nontrivial
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (R := F) (by rw [h.finrank_eq]; norm_num)

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in

theorem _root_.GlobalTheory.RegSS.quad_exists_basis [CharZero F]
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ σ (b 1) = - b 1 ∧ d ≠ 0 ∧
      b 1 * b 1 = algebraMap F E d := by
  have hfr := h.finrank_eq
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hfr]; norm_num)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  haveI := h.etale
  haveI : IsReduced E := Algebra.FormallyUnramified.isReduced_of_field F E
  obtain ⟨e, he⟩ := h.ne_id
  set w := e - σ e with hw
  have hσw : σ w = -w := by simp [w, h.invol]
  have hw0 : w ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have two : (2 : F) ≠ 0 := two_ne_zero
  have hkill : ∀ t : F, t • w = -(t • w) → t = 0 := by
    intro t ht
    have h2 : (2 : F) • (t • w) = 0 := by rw [two_smul]; nth_rewrite 1 [ht]; exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two
    · exact (smul_eq_zero.mp h2).resolve_right hw0
  have hli : LinearIndependent F ![(1 : E), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσst := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσw, map_zero, smul_neg] at hσst
    have ht : t • w = -(t • w) := by
      have := hst.trans hσst.symm
      exact add_left_cancel this
    have ht0 := hkill t ht
    subst ht0
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    rw [Algebra.smul_def, mul_one] at hst
    exact (algebraMap F E).injective (by rw [hst, map_zero])
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = w := by simp [b]
  have hsum : w * w = b.repr (w * w) 0 • (1 : E) + b.repr (w * w) 1 • w := by
    have := b.sum_repr (w * w)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hσ2 : σ (w * w) = w * w := by rw [map_mul, hσw, neg_mul_neg]
  have hc1 : b.repr (w * w) 1 = 0 := by
    apply hkill
    have := congrArg σ hsum
    rw [hσ2] at this
    simp only [map_add, map_smul, map_one, hσw, smul_neg] at this
    have := hsum.symm.trans this
    exact add_left_cancel this
  refine ⟨b, b.repr (w * w) 0, hb0, by rw [hb1, hσw], ?_, ?_⟩
  · intro hd
    rw [hc1, hd, zero_smul, zero_smul, add_zero] at hsum
    exact hw0 (IsReduced.eq_zero w ⟨2, by rw [pow_two, hsum]⟩)
  · rw [hb1]
    conv_lhs => rw [hsum, hc1, zero_smul, add_zero, Algebra.smul_def, mul_one]

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.RegSS.inclE_conj (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]
    (x : E) : _root_.Formalism.UG.inclE (F := F) R (σ x) = _root_.Formalism.UG.sigR σ R (_root_.Formalism.UG.inclE (F := F) R x) := by
  simp [_root_.Formalism.UG.inclE, _root_.Formalism.UG.sigR]

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.RegSS.sigR_sigR (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R]
    [Algebra F R] (x : E ⊗[F] R) : _root_.Formalism.UG.sigR σ R (_root_.Formalism.UG.sigR σ R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e r => simp [_root_.Formalism.UG.sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in

theorem _root_.GlobalTheory.RegSS.continuous_rTensor {B B' : Type} [CommRing B] [Algebra F B]
    [CommRing B'] [Algebra F B'] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (f : B →ₗ[F] B') :
    @Continuous _ _ (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B) R) (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B') R)
      (LinearMap.rTensor R f) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B) (B := R)
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B') (B := R)
  letI : TopologicalSpace (B ⊗[F] R) := moduleTopology R (B ⊗[F] R)
  letI : TopologicalSpace (B' ⊗[F] R) := moduleTopology R (B' ⊗[F] R)
  haveI : IsModuleTopology R (B ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (B' ⊗[F] R) := ⟨rfl⟩
  haveI : ContinuousAdd (B' ⊗[F] R) := IsModuleTopology.toContinuousAdd R _
  haveI : ContinuousSMul R (B' ⊗[F] R) := IsModuleTopology.toContinuousSMul R _
  let g : B ⊗[F] R →ₗ[R] B' ⊗[F] R :=
    { toFun := LinearMap.rTensor R f
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, RingHom.id_apply]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b s =>
          show LinearMap.rTensor R f (((1 : B) ⊗ₜ[F] r) * b ⊗ₜ[F] s) =
            ((1 : B') ⊗ₜ[F] r) * f b ⊗ₜ[F] s
          simp
        | add x y hx hy => simp only [mul_add, map_add, hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap g

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.RegSS.continuous_sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] :
    @Continuous _ _ (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := E) R) (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := E) R)
      (_root_.Formalism.UG.sigR σ R) := by
  have hσR : (_root_.Formalism.UG.sigR σ R : E ⊗[F] R → E ⊗[F] R) = LinearMap.rTensor R σ.toLinearMap := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e r => simp [_root_.Formalism.UG.sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hσR]
  exact _root_.GlobalTheory.RegSS.continuous_rTensor R _

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in

theorem _root_.GlobalTheory.RegSS.etale_of_isReduced [CharZero F] (B : Type) [CommRing B]
    [Algebra F B] [Module.Finite F B] [IsReduced B] : Algebra.Etale F B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite F B
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  letI : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I =>
    Ideal.Quotient.field I.asIdeal
  exact ⟨MaximalSpectrum B, inferInstance, fun I => B ⧸ I.asIdeal, inferInstance, inferInstance,
    (IsArtinianRing.equivPi B).restrictScalars F, fun I => ⟨inferInstance, inferInstance⟩⟩

variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E} in
theorem _root_.GlobalTheory.RegSS.genAlg_isReduced
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ) (hA : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ) :
    IsReduced (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) := by
  have := h.quad.etale
  have := hA.2.1
  have : Algebra.Etale F (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) :=
    Algebra.Etale.comp F E _
  exact Algebra.FormallyUnramified.isReduced_of_field F _

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E} in

theorem _root_.GlobalTheory.RegSS.exists_adjEquiv (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ)
    (hA : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ) :
    ∃ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) ≃ₐ[F]
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E),
      (∀ l, (τ l : Matrix n n E) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J (l : Matrix n n E)) ∧
      (∀ l, τ (τ l) = l) ∧
      (∀ e : E, τ (algebraMap E _ e) = algebraMap E _ (σ e)) ∧
      ∀ l, l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ↔ τ l = l := by
  have hJ := h.nondeg
  have hH := h.herm
  have hσ := h.quad.invol
  have hpres := hA.2.2.2.2.1
  let f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) →
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) :=
    fun l => ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J l, hpres l l.2⟩
  have hf : ∀ l, (f l : Matrix n n E) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J l := fun _ => rfl
  let τ0 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) →ₐ[F]
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E) :=
    { toFun := f
      map_one' := Subtype.ext (by rw [hf]; exact _root_.GlobalTheory.RegSS.adj_one _ hJ)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc := congrArg Subtype.val (mul_comm (f b) (f a))
        simp only [MulMemClass.coe_mul, hf] at hc ⊢
        rw [_root_.GlobalTheory.RegSS.adj_mul _ hJ, hc]
      map_zero' := Subtype.ext (by rw [hf]; exact _root_.GlobalTheory.RegSS.adj_zero _ _)
      map_add' := fun a b => Subtype.ext (by
        simp only [AddMemClass.coe_add, hf]
        exact _root_.GlobalTheory.RegSS.adj_add _ _ _ _)
      commutes' := fun c => by
        apply Subtype.ext
        rw [hf, IsScalarTower.algebraMap_apply F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) c]
        simp only [Subalgebra.coe_algebraMap]
        rw [_root_.GlobalTheory.RegSS.adj_algebraMap _ hJ]
        simp }
  have hτ0 : ∀ l, τ0 (τ0 l) = l := fun l =>
    Subtype.ext (_root_.GlobalTheory.RegSS.adj_adj _ (fun x => hσ x) hH hJ l)
  refine ⟨AlgEquiv.ofAlgHom τ0 τ0 (AlgHom.ext hτ0) (AlgHom.ext hτ0), fun l => rfl, hτ0, ?_, ?_⟩
  · intro e
    apply Subtype.ext
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        ((algebraMap E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) e : Matrix n n E)) = _
    simp only [Subalgebra.coe_algebraMap]
    exact _root_.GlobalTheory.RegSS.adj_algebraMap _ hJ e
  · intro l
    rw [Subtype.ext_iff]
    change _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J = J * l ↔
      J⁻¹ * _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J = l
    constructor
    · intro hl
      rw [Matrix.mul_assoc, hl, Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    · intro hl
      calc _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J
          = J * (J⁻¹ * _root_.Formalism.UG.cT (σ : E →+* E) (l : Matrix n n E) * J) := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]
        _ = J * l := by rw [hl]

open Matrix NumberField in
open scoped TensorProduct in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E} in
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E} in

theorem _root_.GlobalTheory.RegSS.plusTensor_tConj (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ)
    (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix n n E) ⊗[F] E) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E)
        (_root_.GlobalTheory.RegSS.tConj _ σ x) : Matrix n n E) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor σ J (γ : Matrix n n E) x : Matrix n n E) := by
  have hJ := h.nondeg
  induction x using TensorProduct.induction_on with
  | zero => simp [_root_.GlobalTheory.RegSS.adj_zero]
  | tmul p e =>
    have hp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj (σ : E →+* E) J
        (((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E))) : Matrix n n E) =
        ((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) : Matrix n n E) := by
      have hp0 : _root_.Formalism.UG.cT (σ : E →+* E)
          (((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E))) : Matrix n n E) * J =
          J * ((p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) : Matrix n n E) := p.2
      simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj]
      rw [Matrix.mul_assoc, hp0, Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    simp only [_root_.GlobalTheory.RegSS.tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusTensor, Algebra.TensorProduct.productMap_apply_tmul,
      Subalgebra.coe_val, IsScalarTower.coe_toAlgHom', MulMemClass.coe_mul,
      Subalgebra.coe_algebraMap]
    rw [_root_.GlobalTheory.RegSS.adj_mul _ hJ, _root_.GlobalTheory.RegSS.adj_algebraMap _ hJ, hp,
      Algebra.commutes]
    rfl
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.GlobalTheory.RegSS.adj_add, hx, hy]

end Quad

end GlobalTheory.RegSS
