import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaIndep

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_anti {U W : Submodule E S.V} (h : U ≤ W) : orth S W ≤ orth S U := by
  intro v hv
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hv ⊢
  exact fun x hx => hv x (h hx)

theorem Hp_le_orth (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Hp Λ F F' ≤ orth S (Xsp F') :=
  orth_anti (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F')

theorem Ylift'_le_orth (Λ : Submodule (𝓞 E) S.V) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Ylift' Λ F F' ≤ orth S (Xsp F') := by
  intro v hv
  have hX : Xsp F' ≤ Xplus F' := (le_sup_left : F'.fl.X ≤ F'.fl.X ⊔ Submodule.span E {F'.fl.z})
  exact orth_anti hX hv.2

theorem mem_ThPairs (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔
      ((p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'') ∧ p.1 - p.2 ∈ Xsp F) ∧ β p.1 - p.2 ∈ Xsp F'' :=
  Iff.rfl

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
  (β₁ β₂ : S.V ≃ₗ[E] S.V)

theorem ThPairs_eq (hΛ : Submodule.IsLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    ThPairs Λ F F' F'' β₁ = ThPairs Λ F F' F'' β₂ := by
  ext p
  rw [mem_ThPairs, mem_ThPairs]
  have hd : p.1 ∈ Hp Λ F F' → β₁ p.1 - β₂ p.1 ∈ Xsp F'' := fun h1 => H p.1 (Hp_le_orth Λ hΛ F F' h1)
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    have e : β₂ p.1 - p.2 = (β₁ p.1 - p.2) - (β₁ p.1 - β₂ p.1) := by abel
    rw [e]
    exact sub_mem h4 (hd h1)
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    have e : β₁ p.1 - p.2 = (β₂ p.1 - p.2) + (β₁ p.1 - β₂ p.1) := by abel
    rw [e]
    exact add_mem h4 (hd h1)

theorem Th_eq (hΛ : Submodule.IsLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    Th Λ F F' F'' β₁ = Th Λ F F' F'' β₂ := by
  unfold Th
  rw [ThPairs_eq Λ F F' F'' β₁ β₂ hΛ H]

theorem s0_eq (hΛ : Submodule.IsLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') (k : ℕ) :
    s0 Λ F F' F'' β₁ k = s0 Λ F F' F'' β₂ k := by
  unfold s0
  rw [Th_eq Λ F F' F'' β₁ β₂ hΛ H]

theorem isScalar_iff (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    IsScalar Λ F F' F'' β₁ ↔ IsScalar Λ F F' F'' β₂ := by
  have key : ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' : S.V,
      (y2'' - β₁ y1' ∈ Xsp F'' ↔ y2'' - β₂ y1' ∈ Xsp F'') := by
    intro y1' hy y2''
    have hd := H y1' (Ylift'_le_orth Λ F F' hy)
    constructor
    · intro h
      have e : y2'' - β₂ y1' = (y2'' - β₁ y1') + (β₁ y1' - β₂ y1') := by abel
      rw [e]
      exact add_mem h hd
    · intro h
      have e : y2'' - β₁ y1' = (y2'' - β₂ y1') - (β₁ y1' - β₂ y1') := by abel
      rw [e]
      exact sub_mem h hd
  unfold IsScalar
  constructor
  · intro h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hb
    exact h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx ((key y1' hy1' y2'').2 hb)
  · intro h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hb
    exact h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx ((key y1' hy1' y2'').1 hb)

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem betaIndep_of (D : D7) (u u' : D.what₂.Word) (h : PI.ScalPairs.BetaL D u u') :
    PI.ScalPairs.BetaFree D u u' := by
  intro hg F0 Λ hR x y hx hy β₁ β₂ h1 h2
  have hΛ : Submodule.IsLattice D.host.E Λ := hR.1.1
  have H := h hg F0 Λ hR x y hx hy β₁ β₂ h1 h2
  exact ⟨s0_eq Λ _ _ _ β₁ β₂ hΛ H _, isScalar_iff Λ _ _ _ β₁ β₂ H⟩

end D7

end PI.UnitaryGroupMassFormula.BetaIndep
