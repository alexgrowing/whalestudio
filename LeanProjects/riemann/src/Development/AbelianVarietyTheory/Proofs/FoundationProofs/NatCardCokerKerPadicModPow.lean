import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

open NumberField IsDedekindDomain in
private lemma natCard_quotient_ker_of_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    (φ : G →+ H) (hφ : Function.Surjective φ) : Nat.card (G ⧸ φ.ker) = Nat.card H :=
  Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.natCard_coker_ker_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (X P : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup P] [Module ℤ_[l] P] (f : X →ₗ[ℤ_[l]] P) (R : Type) [CommRing R] (X' P' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup P'] [Module R P'] (f' : X' →ₗ[R] P') (πX : X →+ X') (πP : P →+ P'), Function.Surjective πX → Function.Surjective πP → (∀ x, πX x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP (f x) = f' (πX x)) → Nat.card ((P ⧸ LinearMap.range f) ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) ((l : ℤ_[l]) ^ r))) = Nat.card (P' ⧸ LinearMap.range f') ∧ ((∀ x p, f x = (l : ℤ_[l]) ^ r • p → ∃ x', f x = (l : ℤ_[l]) ^ r • f x') → Nat.card (LinearMap.ker f ⧸ (LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))).comap (LinearMap.ker f).subtype) = Nat.card (LinearMap.ker f')) := by
  intro l _ r X P _ _ _ _ f R _ X' P' _ _ _ _ f' πX πP hX hP hkX hkP hcomm
  set c : ℤ_[l] := (l : ℤ_[l]) ^ r with hc
  have hrange : ∀ p : P, πP p ∈ LinearMap.range f' ↔ ∃ x y, p = f x + c • y := by
    intro p
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (p - f x) = 0 := by rw [map_sub, hcomm, hx', sub_self]
      obtain ⟨y, hy⟩ := (hkP _).1 h0
      exact ⟨x, y, by rw [hy]; abel⟩
    · rintro ⟨x, y, rfl⟩
      refine ⟨πX x, ?_⟩
      rw [← hcomm, map_add, (hkP (c • y)).2 ⟨y, rfl⟩, add_zero]
  constructor
  · let φ₁ : P →+ (P ⧸ LinearMap.range f) ⧸
        LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c) :=
      ((LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c)).mkQ.comp
        (LinearMap.range f).mkQ).toAddMonoidHom
    let φ₂ : P →+ P' ⧸ LinearMap.range f' := (LinearMap.range f').mkQ.toAddMonoidHom.comp πP
    have hφ₁ : Function.Surjective φ₁ :=
      (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
    have hφ₂ : Function.Surjective φ₂ := (Submodule.mkQ_surjective _).comp hP
    have hker : φ₁.ker = φ₂.ker := by
      ext p
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
      change Submodule.Quotient.mk (Submodule.Quotient.mk p) = 0 ↔
        Submodule.Quotient.mk (πP p) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, hrange]
      constructor
      · rintro ⟨q, hq⟩
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        obtain ⟨x, hx⟩ := hq
        exact ⟨-x, y, by rw [map_neg, hx]; abel⟩
      · rintro ⟨x, y, rfl⟩
        refine ⟨Submodule.Quotient.mk y, ?_⟩
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        exact ⟨-x, by rw [map_neg]; abel⟩
    rw [← natCard_quotient_ker_of_surjective φ₁ hφ₁, ← natCard_quotient_ker_of_surjective φ₂ hφ₂,
      hker]
  · intro hdiv
    let ψ : LinearMap.ker f →+ LinearMap.ker f' :=
      { toFun := fun x => ⟨πX x, by
          rw [LinearMap.mem_ker, ← hcomm, LinearMap.mem_ker.1 x.2, map_zero]⟩
        map_zero' := by ext; simp
        map_add' := fun x y => by ext; simp }
    have hψ : Function.Surjective ψ := by
      rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (f x) = 0 := by rw [hcomm]; exact hx'
      obtain ⟨p, hp⟩ := (hkP _).1 h0
      obtain ⟨x₁, hx₁⟩ := hdiv x p hp.symm
      refine ⟨⟨x - c • x₁, by rw [LinearMap.mem_ker, map_sub, map_smul, ← hx₁, sub_self]⟩, ?_⟩
      ext
      change πX (x - c • x₁) = πX x
      rw [map_sub, (hkX (c • x₁)).2 ⟨x₁, rfl⟩, sub_zero]
    have hker : ψ.ker = ((LinearMap.range (LinearMap.lsmul ℤ_[l] X c)).comap
        (LinearMap.ker f).subtype).toAddSubgroup := by
      ext x
      rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
        LinearMap.mem_range]
      change (⟨πX x, _⟩ : LinearMap.ker f') = 0 ↔ _
      rw [Subtype.ext_iff, ZeroMemClass.coe_zero, hkX]
      simp [LinearMap.lsmul_apply]
    have h := natCard_quotient_ker_of_surjective ψ hψ
    rw [hker] at h
    exact h

end GlobalTheory
