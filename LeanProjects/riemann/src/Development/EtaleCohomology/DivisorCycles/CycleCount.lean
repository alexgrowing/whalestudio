import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

def Proj : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (X : Mat C N) (e : Fin n → C), Function.Injective e → Deg n X →
  (∀ i, X.charpoly.IsRoot (e i)) →
  ∃ p : Fin n → Mat C N, Sys p ∧ X = ∑ i, e i • p i ∧ ∀ i, p i ∈ Algebra.adjoin C ({X} : Set (Mat C N))

def Grade : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N) (e : Fin n → C)
  (g : Submodule C (Mat C N)), Sys p → IsLac e →
  (∀ Y ∈ g, (∑ i, e i • p i) * Y - Y * (∑ i, e i • p i) ∈ g) → ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g

def CycleCount : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Deg n y → Disj y π p →
  HasEig n y ∧ ∀ i, π i = i → ∃ c : C, y * p i = c • p i

def DiagScalar : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (e : Fin n → C) (Y : Mat C N), Sys p → Function.Injective e → (∀ i, Y * p i = p i * Y) →
  (∀ s : C, Deg n (s • Y + ∑ i, e i • p i)) → ∀ i, ∃ c : C, Y * p i = c • p i

def AlgStruct : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (g : Submodule C (Mat C N)), Sys p →
  (∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g) → (∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g) →
  (∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) →
  ∀ a ∈ Algebra.adjoin C (g : Set (Mat C N)),
    (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i

def Semis : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)),
  IsSSMat ρ → Normd ρ A → Keeps ρ A → NoNil A

def MatrixUnits₂ : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N),
  Sys p → Corner A p → NoNil A → ∃ E, MUnits A p E

def IdemConj : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (A : Subalgebra C (Mat C N))
  (p q : Fin n → Mat C N), Sys p → Corner A p → Sys q → Corner A q → NoNil A →
  ∃ v ∈ A, IsUnit v ∧ ∃ π : Equiv.Perm (Fin n), (∀ j, v * p j = q (π j) * v) ∧
    ∀ i, (∃ a ∈ A, q i * a * p i ≠ 0) → π i = i

def UnitFactorization : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
  (E : Fin n → Fin n → Mat C N), Sys p → MUnits A p E → ∀ v ∈ A, IsUnit v →
  ∃ u ∈ Tv A p, ∃ d : Fin n → C, (∀ j, d j ≠ 0) ∧ v = u * ∑ j, d j • p j

def GenSpec : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (x : Mat C N) (π : Equiv.Perm (Fin n)),
  Sys p → IsUnit x → (∀ j, x * p j = p (π j) * x) → ∃ B : Set C, B.Finite ∧ ∀ τ : Fin n → C, (∀ j, τ j ≠ 0) →
    MulLac τ B → Disj (x * ∑ j, τ j • p j) π p

def Struct : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (X : Mat C N) (e : Fin n → C), IsSSMat ρ → (∀ g, Deg n (ρ g : Mat C N)) → X ∈ lie ρ →
  IsLac e → (∀ i, X.charpoly.IsRoot (e i)) → ∃ p, Good ρ e p

def Key : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (e : Fin n → C) (p : Fin n → Mat C N), (∀ g, Deg n (ρ g : Mat C N)) → IsLac e → Good ρ e p →
  ∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g,
    (∃ m ∈ Zcl (img ρ U : Set (Mat C N)), HasEig n ((ρ g : Mat C N) * m)) ∧
    ∀ i, (∃ a ∈ env ρ, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ env ρ, p i * (ρ g : Mat C N) = p i * w

def BigCorner : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N), Corner A p → Normd ρ A → Keeps ρ A →
  (∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w) →
  ∃ R : Subalgebra C (Mat C N), (∀ g, (ρ g : Mat C N) ∈ R) ∧ Corner R p ∧ Normd ρ R ∧ Keeps ρ R

def Rep : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C) (R : Subalgebra C (Mat C N))
  (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N), Sys p → MUnits R p E → (∀ g, (ρ g : Mat C N) ∈ R) →
  ∃ r A B, Sub (n := n) ρ r A B

def DenseAlg : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [CharZero C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (r : Γ →* GL (Fin n) C) A B, Sub ρ r A B → ∀ (U : Subgroup Γ) (g : Γ), ∀ m ∈ Zcl (img ρ U : Set (Mat C N)),
  HasEig n ((ρ g : Mat C N) * m) → ∃ u ∈ U, (r (g * u) : Mat C n).charpoly.Separable

def DegAll : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K), Continuous (fun g => (ρ g : Mat K N)) →
  ∀ S : Set Γ, Dense S → (∀ s ∈ S, Deg n (ρ s : Mat K N)) → ∀ g, Deg n (ρ g : Mat K N)

def FinSub : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r ∧ A.rank = n ∧ (∀ g, (r g : Mat K n) = B * (ρ g : Mat K N) * A) ∧
  ∀ g (q : Polynomial K), Polynomial.aeval (ρ g : Mat K N) q = 0 ↔ Polynomial.aeval (r g : Mat K n) q = 0

def FinEmbed : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r →
  ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
    (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧ (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧
    ∑ j, T' j * T j = 1

def FinDense : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] (n : ℕ) (r : Γ →* GL (Fin n) K),
  Continuous (fun g => (r g : Mat K n)) →
  (∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g, ∃ u ∈ U, (r (g * u) : Mat K n).charpoly.Separable) →
  IsOpen {g | (r g : Mat K n).charpoly.Separable} ∧ Dense {g | (r g : Mat K n).charpoly.Separable}

def FinPoly : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (x : Mat K n) (P : Polynomial K), P.Monic →
  P.natDegree = n → Polynomial.aeval x P = 0 → (x.charpoly.Separable → x.charpoly = P) ∧
  (ProdGen n P → x.det = (-1) ^ n * P.coeff 0 → x.charpoly = P)

end LateralTheory.DivDb
