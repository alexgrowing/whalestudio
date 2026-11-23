import Mathlib

universe u

namespace Formalism.ELL

def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b

def QuadHyp {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T) : Prop :=
  (∀ a a' b : M, quadDiff φ (a + a') b - quadDiff φ a b - quadDiff φ a' b ∈ N) ∧
  φ 0 ∈ N ∧
  (∀ (α : O) (t : M), φ (α • t) - nrm α • φ t ∈ N) ∧
  (∀ (α : O) (a b : M), quadDiff φ (α • a) b - quadDiff φ a (bar α • b) ∈ N)

def IsoExpand : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∑ i, φ (∑ e, y e i • t e))
        - ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
            + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
                quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) ∈ N

def IsoVanish : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∀ e e', ∑ i, bar (y e i) * y e' i = 0) → (∀ e, ∑ i, nrm (y e i) = 0) →
        (∑ i, φ (∑ e, y e i • t e)) ∈ N

end Formalism.ELL
