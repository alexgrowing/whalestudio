import Mathlib

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def LocPrincipal {A : Type} [CommRing A] (I p : Ideal A) : Prop :=
  ∃ t f : A, t ∉ p ∧ f ∈ I ∧ f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}

theorem locPrincipal_span {A : Type} [CommRing A] {f : A} (hf : f ≠ 0) {p : Ideal A} (hp : p ≠ ⊤) :
    LocPrincipal (Ideal.span {f}) p :=
  ⟨1, f, fun h => hp ((Ideal.eq_top_iff_one p).2 h), Ideal.mem_span_singleton_self f, hf,
    fun g hg => ⟨0, by simpa using hg⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
