import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMkOfComp

namespace GlobalTheory

theorem locPullback_side {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (s : A) [IsLocalization.Away s LA] (φ : A →+* R)
    [IsLocalization.Away (φ s) LR] (Φ : LA →+* LR)
    (hΦ : Φ.comp (algebraMap A LA) = (algebraMap R LR).comp φ)
    (x : LR) (a₀ : A) (r : R) (j k e : ℕ) (he : j + k = e)
    (hx : x * algebraMap R LR (φ s ^ k) = algebraMap R LR r) (ha : φ a₀ = r * φ s ^ j) :
    Φ (IsLocalization.mk' LA a₀ (⟨s ^ e, e, rfl⟩ : Submonoid.powers s)) = x := by
  subst he
  have hΦ' : ∀ y, Φ (algebraMap A LA y) = algebraMap R LR (φ y) := fun y => RingHom.congr_fun hΦ y
  have hs := IsLocalization.mk'_spec LA a₀ (⟨s ^ (j + k), j + k, rfl⟩ : Submonoid.powers s)
  have h2 := congrArg Φ hs
  simp only [map_mul, hΦ'] at h2
  rw [ha, map_pow] at h2
  apply (IsLocalization.map_units LR (⟨φ s ^ (j + k), j + k, rfl⟩ : Submonoid.powers (φ s))).mul_left_inj.mp
  show _ * algebraMap R LR (φ s ^ (j + k)) = x * algebraMap R LR (φ s ^ (j + k))
  rw [h2, map_mul, ← hx, pow_add, map_mul]
  ring

theorem localization_pullback_square_of_lift {A R₀ A' B₀ : Type} [CommRing A] [CommRing R₀] [CommRing A'] [CommRing B₀]
    (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀) (hsq : α.comp φ = κ.comp ψ)
    (hinj : ∀ a, φ a = 0 → ψ a = 0 → a = 0) (hlift : ∀ r c, α r = κ c → ∃ a, φ a = r ∧ ψ a = c)
    (s : A) (LA LR LA' LB : Type) [CommRing LA] [CommRing LR] [CommRing LA'] [CommRing LB]
    [Algebra A LA] [Algebra R₀ LR] [Algebra A' LA'] [Algebra B₀ LB]
    [IsLocalization.Away s LA] [IsLocalization.Away (φ s) LR] [IsLocalization.Away (ψ s) LA']
    [IsLocalization.Away (α (φ s)) LB]
    (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB)
    (hΦ : Φ.comp (algebraMap A LA) = (algebraMap R₀ LR).comp φ)
    (hΨ : Ψ.comp (algebraMap A LA) = (algebraMap A' LA').comp ψ)
    (hA : Aα.comp (algebraMap R₀ LR) = (algebraMap B₀ LB).comp α)
    (hK : Kκ.comp (algebraMap A' LA') = (algebraMap B₀ LB).comp κ) :
    (∀ t, Φ t = 0 → Ψ t = 0 → t = 0) ∧ ∀ a b, Aα a = Kκ b → ∃ t, Φ t = a ∧ Ψ t = b := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.QuotientMapComposition.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.QuotientMapComposition.main
  | exact @_root_.GlobalTheory.QuotientMapComposition.main
  | exact _root_.GlobalTheory.QuotientMapComposition.main
  | (apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMapComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMapComposition.main ..)

theorem locPullback : ∀ {A R₀ A' B₀ : Type} [CommRing A] [CommRing R₀] [CommRing A'] [CommRing B₀]
    (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), α.comp φ = κ.comp ψ →
    (∀ a, φ a = 0 → ψ a = 0 → a = 0) → (∀ r c, α r = κ c → ∃ a, φ a = r ∧ ψ a = c) →
    ∀ (s : A) (LA LR LA' LB : Type) [CommRing LA] [CommRing LR] [CommRing LA'] [CommRing LB]
    [Algebra A LA] [Algebra R₀ LR] [Algebra A' LA'] [Algebra B₀ LB]
    [IsLocalization.Away s LA] [IsLocalization.Away (φ s) LR] [IsLocalization.Away (ψ s) LA']
    [IsLocalization.Away (α (φ s)) LB]
    (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB),
    Φ.comp (algebraMap A LA) = (algebraMap R₀ LR).comp φ →
    Ψ.comp (algebraMap A LA) = (algebraMap A' LA').comp ψ →
    Aα.comp (algebraMap R₀ LR) = (algebraMap B₀ LB).comp α →
    Kκ.comp (algebraMap A' LA') = (algebraMap B₀ LB).comp κ →
    (∀ t, Φ t = 0 → Ψ t = 0 → t = 0) ∧ ∀ a b, Aα a = Kκ b → ∃ t, Φ t = a ∧ Ψ t = b := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.QuotientMapComposition.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.QuotientMapComposition.main
  | exact @_root_.GlobalTheory.QuotientMapComposition.main
  | exact _root_.GlobalTheory.QuotientMapComposition.main
  | (apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMapComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMapComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMapComposition.main ..)

end GlobalTheory
