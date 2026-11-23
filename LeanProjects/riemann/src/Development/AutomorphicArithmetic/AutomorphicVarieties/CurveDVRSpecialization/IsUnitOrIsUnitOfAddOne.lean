import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

namespace UpperTheory.V.Pr

open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

abbrev gm {G R : Type} [Group G] [CommRing R] {n : ℕ} (r : G →* GL (Fin n) R) (g : G) : Matrix (Fin n) (Fin n) R := r g

noncomputable def chPoly {G R ι : Type} [Group G] [CommRing R] [Fintype ι] (χ : ι → G →* Rˣ) (g : G) : R[X] :=
  ∏ i, (X - C ((χ i g : Rˣ) : R))

def CharPerm : Prop :=
  ∀ (G k : Type) [Group G] [Field k] (n : ℕ) (χ χ' : Fin n → G →* kˣ), (∀ g, chPoly χ g = chPoly χ' g) →
    ∃ σ : Equiv.Perm (Fin n), ∀ i, χ' i = χ (σ i)

def NotIrrOfChar : Prop :=
  ∀ (G κ : Type) [Group G] [Field κ] (n : ℕ), 2 ≤ n → ∀ (r : G →* GL (Fin n) κ) (χ : Fin n → G →* κˣ),
    (∀ g, (gm r g).charpoly = chPoly χ g) → ¬ MatIrr ⊤ (gm r)

def CliffPrime : Prop :=
  ∀ (G κ : Type) [Group G] [Field κ] [IsAlgClosed κ] (n : ℕ), n.Prime → ∀ (r : G →* GL (Fin n) κ), MatIrr ⊤ (gm r) →
    ∀ (U : Subgroup G) [U.Normal], MatIrr U (gm r) ∨ (∀ u ∈ U, ∃ a : κ, gm r u = a • (1 : Matrix (Fin n) (Fin n) κ)) ∨
      ∃ (b : Module.Basis (Fin n) κ (Fin n → κ)) (la : Fin n → U →* κˣ) (π : G →* Equiv.Perm (Fin n)),
        Function.Injective la ∧ (∀ i (u : U), gm r u *ᵥ b i = ((la i u : κˣ) : κ) • b i) ∧
        (∀ g i, ∃ a : κ, gm r g *ᵥ b i = a • b (π g i)) ∧ ∀ i j, ∃ g, π g i = j

def RedTo {G κ k B : Type} [Group G] [Field κ] [Field k] [CommRing B] {n : ℕ} (r : G →* GL (Fin n) κ)
    (j : B →+* κ) (φ : B →+* k) (χ : Fin n → G →* kˣ) : Prop :=
  ∀ g, ∃ p : B[X], p.map j = (gm r g).charpoly ∧ p.map φ = chPoly χ g

def IrrNormal : Prop :=
  ∀ (G κ k B : Type) [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing B] (n : ℕ), n.Prime →
    ∀ (r : G →* GL (Fin n) κ), MatIrr ⊤ (gm r) → ∀ (j : B →+* κ) (φ : B →+* k) (χ : Fin n → G →* kˣ),
    Function.Injective j → RedTo r j φ χ → ∀ (D : Type) [Group D] (ι : D →* G) (ψ : Fin n → D →* κˣ),
    (∀ g, (gm r (ι g)).charpoly = chPoly ψ g) → ∀ (U : Subgroup G) [U.Normal],
    (∀ a b, a ≠ b → ∃ g, ι g ∈ U ∧ ψ a g ≠ ψ b g) → (∃ a b g, χ a (ι g) ≠ χ b (ι g)) → MatIrr U (gm r)

def LinClosed {G κ : Type} [TopologicalSpace G] [Field κ] {n : ℕ} (a : G → Matrix (Fin n) (Fin n) κ) : Prop :=
  ∀ f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ, IsClosed {g | f (a g) = 0}

def LinClosedOfAdic : Prop :=
  ∀ (G A κ : Type) [TopologicalSpace G] [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [Field κ]
    (j : A →+* κ), Function.Injective j → ∀ (n : ℕ) (a : G → Matrix (Fin n) (Fin n) A),
    (∀ s t, AdicCont (maximalIdeal A) fun g => a g s t) → LinClosed fun g => (a g).map j

def IrrProcyclic : Prop :=
  ∀ (G κ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Field κ] [IsAlgClosed κ]
    (n : ℕ), n.Prime → ∀ (r : G →* GL (Fin n) κ), LinClosed (gm r) →
    (∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr U (gm r)) → ∀ (Z : Subgroup G) [Z.Normal] (g : G),
    (Z ⊔ Subgroup.zpowers g).topologicalClosure = ⊤ → MatIrr Z (gm r)

def StrongIrr {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) : Prop :=
  ∀ (W : Submodule κ (Fin n → κ)) (S : Subgroup G), S.FiniteIndex → (∀ g, g ∈ S ↔ ∀ v ∈ W, gm r g *ᵥ v ∈ W) →
    W = ⊥ ∨ W = ⊤

def StrongIrrOfOpen : Prop :=
  ∀ (G κ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Field κ] (n : ℕ) (r : G →* GL (Fin n) κ),
    LinClosed (gm r) → (∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr U (gm r)) → StrongIrr r

def FreeRatios {κ ι : Type} [Field κ] (α : ι → κˣ) : Prop := ∀ i j, i ≠ j → ∀ m : ℕ, 0 < m → α i ^ m ≠ α j ^ m

def CommonFree : Prop :=
  ∀ (H A ι : Type) [Group H] [CommGroup A] [Finite ι] (χ : ι → H →* A) (N : ℕ), 0 < N →
    (∀ i h (m : ℕ), 0 < m → χ i h ^ m = 1 → χ i h ^ N = 1) → (∀ i, ∃ h, χ i h ^ N ≠ 1) →
    ∃ h, ∀ i (m : ℕ), 0 < m → χ i h ^ m ≠ 1

def ExpSums : Prop :=
  ∀ (κ ι σ : Type) [Field κ] [Fintype ι] [Finite σ] (α : σ → ι → κˣ) (c : σ → ι → κ), (∀ s, FreeRatios (α s)) →
    (∀ s, ∃ i, c s i ≠ 0) → ∃ m : ℕ, ∀ s, ∑ i, c s i * ((α s i : κˣ) : κ) ^ m ≠ 0

def Full {κ : Type} [Field κ] {n : ℕ} (b : GL (Fin n) κ) : Prop :=
  ∀ i j, (b : Matrix (Fin n) (Fin n) κ) i j ≠ 0 ∧ ((b⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j ≠ 0

def FullEx : Prop :=
  ∀ (G κ : Type) [Group G] [Field κ] (n : ℕ) (r : G →* GL (Fin n) κ), StrongIrr r →
    ∀ (u : G) (α : Fin n → κˣ), FreeRatios α → gm r u = diagonal (fun i => ((α i : κˣ) : κ)) → ∃ b, Full (r b)

def SepOfMinors : Prop :=
  ∀ (κ : Type) [Field κ] (n : ℕ), n ≤ 3 → ∀ (y : Matrix (Fin n) (Fin n) κ) (α : Fin n → κˣ), FreeRatios α →
    (∀ S : Finset (Fin n), (y.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0) →
    ∃ m : ℕ, (y * diagonal (fun i => ((α i : κˣ) : κ)) ^ m).charpoly.Separable

def RegCoset : Prop :=
  ∀ (G κ : Type) [Group G] [Field κ] (n : ℕ), n ≤ 3 → ∀ (r : G →* GL (Fin n) κ), StrongIrr r →
    ∀ (u : G) (α : Fin n → κˣ), FreeRatios α → (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)) →
    ∀ y : GL (Fin n) κ, ∃ h, ((y : Matrix (Fin n) (Fin n) κ) * gm r h).charpoly.Separable

def RegCosetE : Prop :=
  ∀ (G κ : Type) [Group G] [Field κ] (σ : G →* GL (Fin 2) κ) (ψ₀ : G →* κˣ), StrongIrr σ →
    ∀ (u : G) (α : Fin 2 → κˣ), FreeRatios ![α 0, α 1, ψ₀ u] → (gm σ u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)) →
    ∀ (y : GL (Fin 2) κ) (z : κˣ), ∃ h,
      (((y : Matrix (Fin 2) (Fin 2) κ) * gm σ h).charpoly * (X - C ((z * ψ₀ h : κˣ) : κ))).Separable

def ConstOfAlg : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A] (x : A) (c : k),
    IsAlgebraic k x → x - algebraMap k A c ∈ maximalIdeal A → x = algebraMap k A c

def ConstOfChar : Prop :=
  ∀ (G k A : Type) [Group G] [Field k] [Finite k] [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A],
    (2 : k) ≠ 0 → ∀ (η : G →* ℤˣ) (Ψ : G →* kˣ) (c g₁ : G), Marks η Ψ c g₁ → ∀ r : G →* GG 3 A, HasMult η r →
    (∀ g, EntIn (maximalIdeal A) ((r g).mat - ((r0 η Ψ g).mat).map (algebraMap k A))) → Normalised c g₁ r →
    ∀ U : Subgroup G, U.FiniteIndex →
    (∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap k A)).charpoly) →
    (Upper η r ∨ Lower η r) ∧ ∀ g a, (r g).mat a a = algebraMap k A ((r0 η Ψ g).mat a a)

class IsCD (O A : Type) [CommRing O] [CommRing A] [Algebra O A] : Prop extends IsDomain A, IsDiscreteValuationRing A where
  complete : IsAdicComplete (maximalIdeal A) A
  isLocalHom : IsLocalHom (algebraMap O A)
  fin : Finite (ResidueField A)

attribute [instance] IsCD.complete IsCD.isLocalHom IsCD.fin

def FinCrit : Prop :=
  ∀ (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R),
    (∀ i, W.z i ∈ maximalIdeal R) →
    (∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] (f : R →ₐ[O] A), IsLocalHom f →
      (∀ a ∈ maximalIdeal O, algebraMap O A a = 0) →
      (∀ i, W.wt i = 0 → f (W.z i) = 0) ∧
        ((∀ i, W.wt i < 0 → f (W.z i) = 0) ∨ ∀ i, 0 < W.wt i → f (W.z i) = 0)) →
    Module.Finite O (W.part 0)

example (l : ℕ) [Fact l.Prime] : IsCD ℤ_[l] ℤ_[l] where
  complete := inferInstance
  isLocalHom := ⟨fun _ h => h⟩
  fin := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv

end UpperTheory.V.Pr
