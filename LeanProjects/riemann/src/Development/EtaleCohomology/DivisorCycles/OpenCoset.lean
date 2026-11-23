import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.DivWCoreLacUseType

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

abbrev Mat (C : Type) (N : ℕ) := Matrix (Fin N) (Fin N) C
abbrev MP (C : Type) [Field C] (N : ℕ) := MvPolynomial (Fin N × Fin N) C

section defs
variable {C : Type} [Field C] {N n : ℕ} {Γ : Type} [Group Γ]
theorem isLac_inj {e : Fin n → C} (h : IsLac e) : Function.Injective e := fun i j hij => by
  by_contra hne
  exact h {i} {j} (by simp) (by simp) (by simpa using hne) (by simp [hij])

noncomputable def ev (x : Mat C N) (f : MP C N) : C := MvPolynomial.eval (fun p => x p.1 p.2) f

noncomputable def dAt (f : MP C N) (x Y : Mat C N) : C := ∑ p, ev x (MvPolynomial.pderiv p f) * Y p.1 p.2
def Van (S : Set (Mat C N)) : Set (MP C N) := {f | ∀ x ∈ S, ev x f = 0}

def Zcl (S : Set (Mat C N)) : Set (Mat C N) := {y | ∀ f ∈ Van S, ev y f = 0}

def Tan (S : Set (Mat C N)) : Submodule C (Mat C N) where
  carrier := {Y | ∀ f ∈ Van S, dAt f 1 Y = 0}
  zero_mem' := fun f _ => by simp [dAt]
  add_mem' := fun {a b} ha hb f hf => by
    have h1 := ha f hf; have h2 := hb f hf
    simp only [dAt, Matrix.add_apply, mul_add, Finset.sum_add_distrib] at *; rw [h1, h2, add_zero]
  smul_mem' := fun c a ha f hf => by
    have h1 := ha f hf
    simp only [dAt, Matrix.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at *; rw [h1, mul_zero]

noncomputable def DX (Y : Mat C N) : Derivation C (MP C N) (MP C N) :=
  MvPolynomial.mkDerivation C (fun p => ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2))

def Deg (n : ℕ) (x : Mat C N) : Prop := ∃ q : Polynomial C, q ≠ 0 ∧ q.natDegree ≤ n ∧ Polynomial.aeval x q = 0

def HasEig (n : ℕ) (x : Mat C N) : Prop := ∃ l : Fin n → C, Function.Injective l ∧ ∀ j, x.charpoly.IsRoot (l j)

def img (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) : Submonoid (Mat C N) :=
  U.toSubmonoid.map ((Units.coeHom (Mat C N)).comp ρ)

def lie (ρ : Γ →* GL (Fin N) C) : Submodule C (Mat C N) := Tan (img ρ ⊤ : Set (Mat C N))

def env (ρ : Γ →* GL (Fin N) C) : Subalgebra C (Mat C N) := Algebra.adjoin C (lie ρ : Set (Mat C N))

def Sys (p : Fin n → Mat C N) : Prop := CompleteOrthogonalIdempotents p ∧ ∀ i, p i ≠ 0

def Corner (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) : Prop :=
  (∀ i, p i ∈ A) ∧ ∀ a ∈ A, ∀ i, ∃ c : C, p i * a * p i = c • p i

def NoNil (A : Subalgebra C (Mat C N)) : Prop := ∀ Y ∈ A, (∀ a ∈ A, IsNilpotent (a * Y)) → Y = 0

def Normd (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Prop :=
  ∀ g, ∀ a ∈ A, (ρ g : Mat C N) * a * (ρ g⁻¹ : Mat C N) ∈ A

def Keeps (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Prop :=
  ∀ W : Submodule C (Fin N → C), (∀ g, ∀ v ∈ W, (ρ g : Mat C N) *ᵥ v ∈ W) → ∀ a ∈ A, ∀ v ∈ W, a *ᵥ v ∈ W

def MUnits (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N) : Prop :=
  (∀ i j, E i j ∈ A) ∧ (∀ i, E i i = p i) ∧ (∀ i j, p i * E i j * p j = E i j) ∧
  (∀ i j, E i j ≠ 0 → E j i ≠ 0) ∧ (∀ i j k, E i j ≠ 0 → E j k ≠ 0 → E i j * E j k = E i k ∧ E i k ≠ 0) ∧
  ∀ a ∈ A, ∀ i j, ∃ c : C, p i * a * p j = c • E i j

def Tv (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) : Submonoid (Mat C N) :=
  Submonoid.closure {u | ∃ a ∈ A, ∃ j k, j ≠ k ∧ u = 1 + p j * a * p k}

def MulLac (τ : Fin n → C) (B : Set C) : Prop := ∀ O O' : Finset (Fin n), O.Nonempty → O'.Nonempty →
  Disjoint O O' → ∀ b ∈ B, (∏ i ∈ O, τ i) ^ O'.card ≠ b * (∏ i ∈ O', τ i) ^ O.card

def Disj (y : Mat C N) (π : Equiv.Perm (Fin n)) (p : Fin n → Mat C N) : Prop :=
  ∀ i j, ¬ π.SameCycle i j → ∀ (l : C) (v w : Fin N → C), v ≠ 0 → w ≠ 0 → y *ᵥ v = l • v → y *ᵥ w = l • w →
    (∀ k, ¬ π.SameCycle i k → p k *ᵥ v = 0) → (∀ k, ¬ π.SameCycle j k → p k *ᵥ w = 0) → False

def Sub (ρ : Γ →* GL (Fin N) C) (r : Γ →* GL (Fin n) C) (A : Matrix (Fin N) (Fin n) C)
    (B : Matrix (Fin n) (Fin N) C) : Prop :=
  B * A = 1 ∧ (∀ g, (ρ g : Mat C N) * A = A * (r g : Mat C n)) ∧
  ∀ Z : Mat C N, (∀ T : Matrix (Fin N) (Fin n) C, (∀ g, (ρ g : Mat C N) * T = T * (r g : Mat C n)) → Z * T = 0) → Z = 0

def Good (ρ : Γ →* GL (Fin N) C) (e : Fin n → C) (p : Fin n → Mat C N) : Prop :=
  Sys p ∧ (∑ i, e i • p i) ∈ lie ρ ∧ Corner (env ρ) p ∧ NoNil (env ρ) ∧ Normd ρ (env ρ) ∧ Keeps ρ (env ρ) ∧
  ∀ a ∈ env ρ, ∀ i j, i ≠ j → p i * a * p j ∈ lie ρ
end defs

def SpecPt : Prop := ∀ (C R σ : Type) [Field C] [IsAlgClosed C] [CommRing R] [IsDomain R] [Algebra C R] [Finite σ]
  (x : σ → R) (G : Set (MvPolynomial σ C)), G.Finite → (∀ g ∈ G, MvPolynomial.aeval x g ≠ 0) →
  ∃ y : σ → C, (∀ f : MvPolynomial σ C, MvPolynomial.aeval x f = 0 → MvPolynomial.eval y f = 0) ∧
    ∀ g ∈ G, MvPolynomial.eval y g ≠ 0

def SpecLie : Prop := ∀ (Γ K K' : Type) [Group Γ] [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) K) (X : Mat K' N) (e : Fin n → K'), InLieZar ρ X → IsLac e → (∀ i, X.charpoly.IsRoot (e i)) →
  ∃ (X₀ : Mat K N) (e₀ : Fin n → K), X₀ ∈ lie ρ ∧ IsLac e₀ ∧ ∀ i, X₀.charpoly.IsRoot (e₀ i)

def Chain : Prop := ∀ (C : Type) [Field C] (N M : ℕ) (φ : Mat C N →ₗ[C] Mat C M) (f : MP C M), ∃ f' : MP C N,
  (∀ x, ev x f' = ev (φ x) f) ∧ ∀ x Y, dAt f' x Y = dAt f (φ x) (φ Y)

def DegPoly : Prop := ∀ (C : Type) [Field C] (N n : ℕ), ∃ 𝓕 : Set (MP C N),
  ∀ (F : Type) [Field F] [Algebra C F] (x : Mat F N),
    Deg n x ↔ ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = 0

def SepPoly : Prop := ∀ (C : Type) [Field C] [CharZero C] (n : ℕ), ∃ f : MP C n,
  ∀ x : Mat C n, x.charpoly.Separable ↔ ev x f ≠ 0

def ZclMul : Prop := ∀ (C : Type) [Field C] (N : ℕ) (S : Submonoid (Mat C N)),
  ∀ x ∈ Zcl (S : Set (Mat C N)), ∀ y ∈ Zcl (S : Set (Mat C N)), x * y ∈ Zcl (S : Set (Mat C N))

def TanField : Prop := ∀ (C : Type) [Field C] (N : ℕ) (S : Submonoid (Mat C N)) (Y : Mat C N),
  Y ∈ Tan (S : Set (Mat C N)) ↔ ∀ f ∈ Van (S : Set (Mat C N)), DX Y f ∈ Van (S : Set (Mat C N))

def TanLie : Prop := ∀ (C : Type) [Field C] (N : ℕ) (S : Submonoid (Mat C N)),
  ∀ Y ∈ Tan (S : Set (Mat C N)), ∀ Z ∈ Tan (S : Set (Mat C N)), Y * Z - Z * Y ∈ Tan (S : Set (Mat C N))

def EnvStab : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C),
  Normd ρ (env ρ) ∧ Keeps ρ (env ρ)

def TanIndex : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ),
  U.Normal → U.FiniteIndex → lie ρ ≤ Tan (img ρ U : Set (Mat C N))

def ExpVan : Prop := ∀ (C : Type) [Field C] [CharZero C] (N : ℕ) (S : Submonoid (Mat C N)),
  ∀ Y ∈ Tan (S : Set (Mat C N)), ∀ f ∈ Van (S : Set (Mat C N)),
    MvPolynomial.aeval (fun p : Fin N × Fin N =>
      PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2) f = 0

def Unip : Prop := ∀ (C : Type) [Field C] [CharZero C] (N : ℕ) (S : Submonoid (Mat C N)),
  ∀ E ∈ Tan (S : Set (Mat C N)), E * E = 0 → 1 + E ∈ Zcl (S : Set (Mat C N))

def TanDeg : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (S : Submonoid (Mat C N)), (∀ x ∈ S, Deg n x) →
  (∀ x ∈ Zcl (S : Set (Mat C N)), Deg n x) ∧ ∀ Y ∈ Tan (S : Set (Mat C N)), Deg n Y

def TorusPt : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (S : Submonoid (Mat C N))
  (p : Fin n → Mat C N) (e : Fin n → C), Sys p → IsLac e → (∑ i, e i • p i) ∈ Tan (S : Set (Mat C N)) →
  ∀ B : Set C, B.Finite → ∃ τ : Fin n → C, (∀ j, τ j ≠ 0) ∧ (∑ j, τ j • p j) ∈ Zcl (S : Set (Mat C N)) ∧ MulLac τ B

def OpenCoset : Prop := ∀ (Γ C : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Field C] (n : ℕ) (r : Γ →* GL (Fin n) C) (f : MP C n) (O : Set Γ), IsOpen O → O.Nonempty →
  (∀ g ∈ O, ev (r g : Mat C n) f = 0) →
  ∃ U : Subgroup Γ, U.Normal ∧ U.FiniteIndex ∧ ∃ g, ∀ u ∈ U, ev (r (g * u) : Mat C n) f = 0

end LateralTheory.DivDb
