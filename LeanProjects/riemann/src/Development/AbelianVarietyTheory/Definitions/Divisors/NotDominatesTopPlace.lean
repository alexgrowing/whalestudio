import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

def NonUnit (R : Subring K) (f : K) : Prop := f ∈ R ∧ (f = 0 ∨ f⁻¹ ∉ R)

def RatRes (c : k →+* K) (R : Subring K) : Prop := ∀ r ∈ R, ∃ a, NonUnit R (r - c a)

def Dominates (ρ : K →+* L) (B : Subring L) (O : Subring K) : Prop :=
  ∀ f ∈ O, ρ f ∈ B ∧ (NonUnit O f → NonUnit B (ρ f))

structure IsEtTower (cK : k →+* K) (R : Subring K) (cL : k →+* L) (T : Subring L) {r : ℕ}
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) : Prop where

  base : IsLocModel cK R

  normal : IsIntegrallyClosed R

  top : IsLocModel cL T

  const : ∀ a, (ι ⟨cK a, base.const_mem a⟩ : L) = cL a

  retr : ∀ a, ψ (ι a) = a

  zero : ∀ i, ψ (τ i) = 0

  etale : (MvPolynomial.eval₂Hom ι τ).FormallyEtale

theorem IsEtTower.refl {c : k →+* K} {R : Subring K} (h : IsLocModel c R)
    (h' : IsIntegrallyClosed R) :
    IsEtTower c R c R (RingHom.id R) (RingHom.id R) (Fin.elim0 : Fin 0 → R) where
  base := h
  normal := h'
  top := h
  const _ := rfl
  retr _ := rfl
  zero i := i.elim0
  etale := by
    have hb : Function.Bijective (MvPolynomial.eval₂Hom (RingHom.id R) (Fin.elim0 : Fin 0 → R)) := by
      refine ⟨fun P Q e => ?_, fun a => ⟨MvPolynomial.C a, by simp⟩⟩
      rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q] at e ⊢
      simpa using e
    letI := (MvPolynomial.eval₂Hom (RingHom.id R) (Fin.elim0 : Fin 0 → R)).toAlgebra
    exact Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId (MvPolynomial (Fin 0) R) R) hb)

set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in

theorem _root_.GlobalTheory.FieldPair.nonUnit_iff {R : Subring K} (f : R) :
    _root_.GlobalTheory.FieldPair.NonUnit R f ↔ ¬ IsUnit f := by
  constructor
  · rintro ⟨-, h0 | hinv⟩ hu
    · have hf : f = 0 := Subtype.ext (by simpa using h0)
      exact not_isUnit_zero (hf ▸ hu)
    · obtain ⟨u, rfl⟩ := hu
      have hmul : ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]
        rfl
      rw [inv_eq_of_mul_eq_one_right hmul] at hinv
      exact hinv (u⁻¹ : Rˣ).1.2
  · intro hnu
    refine ⟨f.2, ?_⟩
    by_contra h
    push_neg at h
    apply hnu
    exact IsUnit.of_mul_eq_one (b := (⟨_, h.2⟩ : R)) (Subtype.ext (by simp [h.1]))

set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in

theorem _root_.GlobalTheory.FieldPair.nonUnit_zero (R : Subring K) : _root_.GlobalTheory.FieldPair.NonUnit R 0 :=
  ⟨R.zero_mem, Or.inl rfl⟩

set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in

theorem _root_.GlobalTheory.FieldPair.not_nonUnit_one (R : Subring K) : ¬ _root_.GlobalTheory.FieldPair.NonUnit R 1 := by
  rintro ⟨-, h | h⟩
  · exact one_ne_zero h
  · exact h (by rw [inv_one]; exact R.one_mem)

theorem Dominates.refl (R : Subring K) : Dominates (RingHom.id K) R R :=
  fun _ hf => ⟨hf, id⟩

set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in

theorem _root_.GlobalTheory.FieldPair.Dominates.trans {M : Type} [Field M] {ρ : K →+* L} {σ : L →+* M}
    {O : Subring K} {B : Subring L} {C : Subring M} (h : _root_.GlobalTheory.FieldPair.Dominates ρ B O)
    (h' : _root_.GlobalTheory.FieldPair.Dominates σ C B) :
    _root_.GlobalTheory.FieldPair.Dominates (σ.comp ρ) C O := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  obtain ⟨h3, h4⟩ := h' (ρ f) h1
  exact ⟨h3, fun hn => h4 (h2 hn)⟩

set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in

theorem _root_.GlobalTheory.FieldPair.ratRes_self : _root_.GlobalTheory.FieldPair.RatRes (RingHom.id k) ⊤ := by
  intro r _
  exact ⟨r, by rw [RingHom.id_apply, sub_self]; exact _root_.GlobalTheory.FieldPair.nonUnit_zero ⊤⟩

end GlobalTheory.FieldPair
