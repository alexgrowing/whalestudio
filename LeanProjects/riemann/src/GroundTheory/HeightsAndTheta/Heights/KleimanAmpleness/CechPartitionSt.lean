import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechPartition.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    {n : ℕ} (U : Finset (Fin n)) (M : Cell U → Submodule S E) (m : ℕ) (a b : Fin m → Ω) (j : Fin m → Fin n),
    (∀ k, j k ∈ U) → ∑ k, a k * b k = 1 →
    (∀ k I, ∀ z ∈ M I, a k • z ∈ M I) → (∀ k I, ∀ z ∈ M I, b k • z ∈ M I) →
    (∀ k (I I' : Cell U), I'.1 = insert (j k) I.1 → ∀ z ∈ M I', ∃ e : ℕ, b k ^ e • z ∈ M I) →
    ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Cell U => E) M (p + 1),
      Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) (p + 1) s = 0 →
        ∃ t ∈ Cech.Cdeg (fun _ : Cell U => E) M p, Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p t = s

end

end GroundTheory.Heights₂.Heights.Kleiman
