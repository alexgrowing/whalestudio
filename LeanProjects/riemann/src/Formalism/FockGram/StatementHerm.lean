import Formalism.FockGram.StatementLat

open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

def HermDual : Prop :=
  ∀ (S K V ι : Type) [CommRing S] [Field K] [StarRing K] [Algebra S K]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V] [Fintype ι] [DecidableEq ι]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V),
    Function.Injective (algebraMap S K) →
    (∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) →
    (Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K)) ∧
    ∀ [Module.Free ℤ S] [Module.Finite ℤ S] (GS : Matrix ι ι S),
      (∀ i j, B (b i) (b j) = algebraMap S K (GS i j)) → GS.det ≠ 0 →
      (Submodule.span S (Set.range b)).toAddSubgroup.relIndex
          (hdual B (Submodule.span S (Set.range b))).toAddSubgroup =
        (Algebra.norm ℤ GS.det).natAbs ∧
      (hdual B (Submodule.span S (Set.range b)) = Submodule.span S (Set.range b) ↔
        IsUnit GS.det)

def HermTraceGram : Prop :=
  ∀ (S M ι κ : Type) [CommRing S] [StarRing S] [AddCommGroup M] [Module S M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : M →ₗ⋆[S] M →ₗ[S] S) (b : Basis ι S M) (ω : Basis κ ℤ S),
    (Matrix.of fun p q : ι × κ => Algebra.trace ℤ S (B (ω p.2 • b p.1) (ω q.2 • b q.1))).det =
      (Matrix.of fun k l : κ => Algebra.trace ℤ S (star (ω k) * ω l)).det ^ Fintype.card ι *
        Algebra.norm ℤ (sgram B b).det

end Formalism.E
