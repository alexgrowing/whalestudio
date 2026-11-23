import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

abbrev addJ {K : Type} (J : K → Type) (N : ℕ) : Unit ⊕ K → Type := Sum.elim (fun _ => Fin (N + 1)) J

instance addJ_fintype {K : Type} (J : K → Type) [∀ k, Fintype (J k)] (N : ℕ) : ∀ k, Fintype (addJ J N k)
  | .inl _ => inferInstanceAs (Fintype (Fin (N + 1)))
  | .inr k => inferInstanceAs (Fintype (J k))

def addY {K : Type} {J : K → Type} {N : ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (y : (Σ k, J k) → Ω₀) (x' : Fin (N + 1) → Ω) : (Σ k, addJ J N k) → Ω
  | ⟨.inl _, a⟩ => x' a
  | ⟨.inr k, a⟩ => algebraMap Ω₀ Ω (y ⟨k, a⟩)

def addV {K : Type} (J : K → Type) (N : ℕ) : (Σ k, J k) → Σ k, addJ J N k := fun p => ⟨.inr p.1, p.2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
