import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.BoundaryPull

open MvPolynomial

theorem coe_aeval_subalgebra {K : Type} [Field K] [CharZero K] {τ : Type}
    (S : Subalgebra ℚ K) (r : τ → K) (h : ∀ p, r p ∈ S) (g : MvPolynomial τ ℤ) :
    ((aeval (fun p => (⟨r p, h p⟩ : S)) g : S) : K) = aeval r g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem vanishing_rename_iff :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' r₀ r₁ v hv bd S S' θ hθ h₀ h₁ q
  have key : ∀ b : MvPolynomial σ ℤ,
      MvPolynomial.aeval r₁ (MvPolynomial.rename v b) = algebraMap Ω₀ Ω (MvPolynomial.aeval r₀ b) := by
    intro b
    induction b using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, hv]
  constructor
  · intro H g hg s hs
    refine Ideal.mem_comap.2 (H (MvPolynomial.rename v g) (Ideal.mem_map_of_mem _ hg) (θ s) ?_)
    rw [hθ, hs, key]
  · intro H g hg s hs
    have claim : ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g := by
      have hspan : g ∈ Ideal.span ((MvPolynomial.rename v : MvPolynomial σ ℤ → MvPolynomial σ' ℤ) '' (bd : Set _)) := hg
      refine Submodule.span_induction (p := fun g _ => ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g)
        ?_ ?_ ?_ ?_ hspan
      · rintro _ ⟨b, hb, rfl⟩
        let s₀ : S := aeval (fun p => (⟨r₀ p, h₀ p⟩ : S)) b
        have hs₀ : (s₀ : Ω₀) = aeval r₀ b := coe_aeval_subalgebra S r₀ h₀ b
        refine ⟨θ s₀, Ideal.mem_comap.1 (H b hb s₀ hs₀), ?_⟩
        rw [hθ, hs₀, key]
      · exact ⟨0, q.zero_mem, by simp⟩
      · rintro x y _ _ ⟨t, ht, hx⟩ ⟨u, hu, hy⟩
        exact ⟨t + u, q.add_mem ht hu, by simp [hx, hy]⟩
      · rintro c x _ ⟨t, ht, hx⟩
        refine ⟨aeval (fun p => (⟨r₁ p, h₁ p⟩ : S')) c * t, q.mul_mem_left _ ht, ?_⟩
        simp [coe_aeval_subalgebra S' r₁ h₁ c, hx]
    obtain ⟨t, ht, hts⟩ := claim
    have : s = t := Subtype.ext (hs.trans hts.symm)
    exact this ▸ ht

end GlobalTheory.CompanionTheory.Ar.BoundaryPull
