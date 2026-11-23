import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open Representation ReciprocityTheory.Gal

namespace Formalism.GaloisCohomology

def DevTorsion : Prop := ∀ (R : Type) [CommRing R] (A B C : Type) [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  (ϖ : R) (c' c'' : ℕ), Function.Exact f g →
  (∀ a, f a = 0 → ∃ k : ℕ, ϖ ^ k • a = 0) →
  (∀ a : A, (∃ k : ℕ, ϖ ^ k • a = 0) → ϖ ^ c' • a = 0) →
  (∀ c : C, (∃ k : ℕ, ϖ ^ k • c = 0) → ϖ ^ c'' • c = 0) →
  ∀ b : B, (∃ k : ℕ, ϖ ^ k • b = 0) → ϖ ^ (c' + c'') • b = 0

def SelMono : Prop := ∀ (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
  (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] (rho : Representation R G M) (I : Type) (D : I → Type)
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (phi : ∀ i, D i →* G)
  (hphi : ∀ i, Continuous (phi i)) (L L' : LocCond rho phi),
  (∀ i, L i ≤ L' i) → Sel rho phi hphi L ≤ Sel rho phi hphi L'

def SelRelaxLen : Prop := ∀ (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
  (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] (rho : Representation R G M) (I : Type) (D : I → Type)
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (phi : ∀ i, D i →* G)
  (hphi : ∀ i, Continuous (phi i)) (L L' : LocCond rho phi) (T : Finset I),
  (∀ i, L i ≤ L' i) → (∀ i ∉ T, L' i ≤ L i) →
    Module.length R (Sel rho phi hphi L') ≤
      Module.length R (Sel rho phi hphi L) +
        ∑ i ∈ T, Module.length R (L' i ⧸ (L i).comap (L' i).subtype)

def ProcycDet : Prop := ∀ (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [T2Space M] (rho : Representation R G M),
  ContAction rho → ∀ g : G, Dense (Subgroup.zpowers g : Set G) →
    (∀ f f' : Z1 rho, f.1 g = f'.1 g → f = f') ∧
    ∃ φ : H1 rho →ₗ[R] M ⧸ LinearMap.range (rho g - LinearMap.id), Function.Injective φ ∧
      ∀ f : Z1 rho, φ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f.1 g)

def ProcycOnto : Prop := ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul ℤ_[l] M]
  (rho : Representation ℤ_[l] (Multiplicative ℤ_[l]) M), ContAction rho →
  IsAdicComplete (Ideal.span {(l : ℤ_[l])}) M →
  (∀ s : Set M, s ∈ nhds (0 : M) ↔
    ∃ r : ℕ, Set.range (fun y : M => ((l : ℤ_[l]) ^ r) • y) ⊆ s) →
  ∀ m : M, ∃ f : Z1 rho, f.1 (Multiplicative.ofAdd 1) = m

end Formalism.GaloisCohomology
