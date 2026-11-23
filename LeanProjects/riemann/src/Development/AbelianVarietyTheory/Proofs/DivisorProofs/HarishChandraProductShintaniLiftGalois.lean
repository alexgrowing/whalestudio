import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLListPropertiesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem deg_of_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    deg L₁ = deg L₂ := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [deg, List.map_cons, List.sum_cons] at ih ⊢
    rw [hab.1, ih]

theorem J_congr_forall₂ {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) {L₁ L₂ : List (ℕ × ℕ)}
    (h : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2) L₁ L₂) :
    J θ L₁ = J θ L₂ := by
  induction h with
  | nil => rfl
  | @cons a b l₁ l₂ hab hl ih =>
    funext n
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    rw [J_cons, J_cons, ih, deg_of_forall₂ θ hl]
    simp only [h2]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem forall₂_flatMap_of {α β : Type} (R : β → β → Prop) (L : List α) (f g : α → List β)
    (h : ∀ p ∈ L, List.Forall₂ R (f p) (g p)) : List.Forall₂ R (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun p hp => h p (by simp [hp]))

theorem cusp_mul_card_pow (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (m K : ℕ) :
    cusp θ m (K * Nat.card F ^ Module.finrank F F') = cusp θ m K := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite F'
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  funext x
  have key := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ (RingEquiv.refl F') (r * Module.finrank F F') (fun y => by
    rw [pow_mul, ← hq, Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
    rfl) m K x
  rw [hq, ← pow_mul, ← key]
  congr 1

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct_frob (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) [Fintype F] (L : List (ℕ × ℕ)) (n : ℕ)
    (hn : n = deg (liftL (Nat.card F) (Module.finrank F F') L)) (x : GL (Fin n) F') :
    J θ (liftL (Nat.card F) (Module.finrank F F') L) n
      (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F') x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have hq : Nat.card F = ringChar F' ^ (r : ℕ) := by rw [Nat.card_eq_fintype_card, hcard, hchar]
  set q := Nat.card F with hqdef
  set l := Module.finrank F F' with hldef
  have hl : 0 < l := Module.finrank_pos
  obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have key := GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow F' θ (FiniteField.frobeniusAlgEquivOfAlgebraic F F').toRingEquiv r (fun y => by
    rw [← hq]
    show (FiniteField.frobeniusAlgEquivOfAlgebraic F F') y = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hqdef, Nat.card_eq_fintype_card]) (liftL q l L) n x
  rw [galAct_apply]
  refine (key.trans ?_)
  rw [← hq]

  set R : List (ℕ × ℕ) := L.flatMap fun p =>
    (List.range l').map (fun i => (p.1 / l, p.2 * q ^ (i + 1))) ++ [(p.1 / l, p.2)] with hR
  have hF : List.Forall₂ (fun p p' : ℕ × ℕ => p.1 = p'.1 ∧ cusp θ p.1 p.2 = cusp θ p.1 p'.2)
      ((liftL q l L).map fun p => (p.1, p.2 * q)) R := by
    rw [liftL, List.map_flatMap, hR]
    apply forall₂_flatMap_of
    intro p _
    rw [hl', List.range_succ, List.map_append, List.map_append]
    simp only [List.map_map, List.map_cons, List.map_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro z _
      refine ⟨rfl, ?_⟩
      simp only [Function.comp_apply, pow_succ, mul_assoc]
    · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      simp only [Function.comp_apply]
      rw [mul_assoc, ← pow_succ, ← hl']
      exact cusp_mul_card_pow F F' θ _ _
  have hP : R.Perm (liftL q l L) := by
    rw [liftL, hR]
    apply List.Perm.flatMap_left
    intro p _
    rw [hl', List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, pow_zero, mul_one]
    refine List.perm_append_comm.trans ?_
    simp [Function.comp_def, ← hl']
  have hdeg : deg R = deg (liftL q l L) := by
    unfold deg
    exact (hP.map Prod.fst).sum_eq
  rw [J_congr_forall₂ θ hF]
  exact ((GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F' θ).2.2 R (liftL q l L) n (hn.trans hdeg.symm) hP) ▸ rfl

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem J_liftL_galAct : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ)
    (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) →
    ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  intro F F' _ _ _ _ θ t L n hn
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  suffices h : ∀ k : ℕ, ∀ x : GL (Fin n) F',
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n
        (galAct F F' n (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ k) x) =
      J θ (liftL (Nat.card F) (Module.finrank F F') L) n x from h i.1
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, map_mul, MulAut.mul_apply, ih]
    exact J_liftL_galAct_frob F F' θ L n hn x

end GlobalTheory.Shin
