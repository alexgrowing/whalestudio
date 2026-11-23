import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem tameGen_image_mem_zpowers {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (γ γ' : G E Ω) (h : TameGenAt A γ) (h' : TameGenAt A γ')
    {M : Type} [Group M] (φ : G E Ω →* M) (hk : IsOpen (φ.ker : Set (G E Ω)))
    (hw : ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) :
    φ γ' ∈ Subgroup.zpowers (φ γ) := by
  have hle : φ.ker ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact Subgroup.one_mem _
  have hop : IsOpen (((Subgroup.zpowers (φ γ)).comap φ : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isOpen_mono hle hk
  have hcl := Subgroup.isClosed_of_isOpen _ hop
  have hsub : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1})
      ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.mem_zpowers _
    · exact hle (hw x hx)
  exact closure_minimal hsub hcl (h.2 h'.1)

theorem tameGen_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ γ' : G E Ω), TameGenAt A γ → TameGenAt A γ' → ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) → ∃ n : ℕ, n.Coprime (orderOf (φ γ)) ∧ 0 < orderOf (φ γ) ∧ φ γ' = φ γ ^ n := by
  intro E Ω _ _ _ _ _ A γ γ' h h' M _ φ hk hw
  have h1 := tameGen_image_mem_zpowers A γ γ' h h' φ hk hw
  have h2 := tameGen_image_mem_zpowers A γ' γ h' h φ hk hw
  haveI : IsGalois E Ω := IsGalois.mk
  haveI : Finite (G E Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hk
  have hfin : IsOfFinOrder (φ γ) := by
    have h0 : IsOfFinOrder (QuotientGroup.mk γ : G E Ω ⧸ φ.ker) := isOfFinOrder_of_finite _
    have := (QuotientGroup.kerLift φ).isOfFinOrder h0
    simpa using this
  have hpos : 0 < orderOf (φ γ) := hfin.orderOf_pos
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).2 h1
  have hn : φ γ ^ n = φ γ' := hn
  have heq : orderOf (φ γ') = orderOf (φ γ) :=
    Nat.dvd_antisymm (orderOf_dvd_of_mem_zpowers h1) (orderOf_dvd_of_mem_zpowers h2)
  refine ⟨n, ?_, hpos, hn.symm⟩
  rw [← hn, hfin.orderOf_pow] at heq
  have hg : (orderOf (φ γ)).gcd n = 1 := by
    rcases Nat.div_eq_self.1 heq with h | h
    · omega
    · exact h
  exact Nat.Coprime.symm hg

end GlobalTheory.TypeLeaf
