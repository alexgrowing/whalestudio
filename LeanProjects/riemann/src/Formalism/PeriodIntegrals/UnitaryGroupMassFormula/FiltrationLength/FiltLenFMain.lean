import Mathlib
import Formalism.PeriodIntegrals.FiltLen
import Formalism.PeriodIntegrals.FiltLenF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.LengthQuotLeOfKerLe

namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem ell_stepF {V : Type} [AddCommGroup V] [Module R V]
    (M N Fk Fk1 : Submodule R W) (ψ : ↥Fk →ₗ[R] V) (P Q : Submodule R V) (hNM : N ≤ M)
    (hinj : ∀ x : ↥Fk, ψ x = 0 → (x : W) ∈ Fk1)
    (hP : (M.comap Fk.subtype).map ψ ≤ P) (hQ : Q ≤ (N.comap Fk.subtype).map ψ) :
    ell (M ⊓ Fk) ((N ⊓ Fk) ⊔ (M ⊓ Fk1)) ≤ Module.length R (↥P ⧸ Q.comap P.subtype) := by
  have hgP : ∀ x : ↥(M ⊓ Fk), ψ (Submodule.inclusion inf_le_right x) ∈ P := fun x =>
    hP (Submodule.mem_map_of_mem (show Submodule.inclusion inf_le_right x ∈ M.comap Fk.subtype from x.2.1))
  let g : ↥(M ⊓ Fk) →ₗ[R] ↥P :=
    LinearMap.codRestrict P (ψ ∘ₗ Submodule.inclusion (inf_le_right : M ⊓ Fk ≤ Fk)) hgP
  let f : ↥(M ⊓ Fk) →ₗ[R] ↥P ⧸ Q.comap P.subtype := (Q.comap P.subtype).mkQ ∘ₗ g
  have hker : LinearMap.ker f ≤ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype := by
    intro x hx
    have hxQ : ψ (Submodule.inclusion inf_le_right x) ∈ Q := by
      have h1 : g x ∈ Q.comap P.subtype := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact h1
    obtain ⟨y, hyN, hyx⟩ := hQ hxQ
    have hdiff : ψ (Submodule.inclusion inf_le_right x - y) = 0 := by rw [map_sub, hyx, sub_self]
    have hF1 := hinj _ hdiff
    have hxM : (x : W) ∈ M := x.2.1
    have hyM : (y : W) ∈ M := hNM hyN
    show (x : W) ∈ (N ⊓ Fk) ⊔ (M ⊓ Fk1)
    have hsplit : (x : W) = (y : W) + ((x : W) - (y : W)) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨hyN, y.2⟩ ⟨M.sub_mem hxM hyM, ?_⟩
    simpa using hF1
  unfold ell
  have hsurj : Function.Surjective (Submodule.factor hker) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  calc Module.length R (↥(M ⊓ Fk) ⧸ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype)
      ≤ Module.length R (↥(M ⊓ Fk) ⧸ LinearMap.ker f) := Module.length_le_of_surjective _ hsurj
    _ ≤ Module.length R (↥P ⧸ Q.comap P.subtype) :=
      Module.length_le_of_injective _
        (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ f le_rfl le_rfl))

theorem filtLenF_main : PI.FiltLenF := by
  intro R W _ _ _ F a hanti h0 ha V _ _ φ hinj M N P Q hNM hP hQ
  set X : ℕ → Submodule R W := fun k => N ⊔ (M ⊓ F k) with hX
  have hXmono : ∀ k, X (k + 1) ≤ X k := fun k =>
    sup_le_sup_left (inf_le_inf_left _ (hanti (Nat.le_succ k))) _
  have hX0 : X 0 = M := by simp [hX, h0, sup_eq_right.2 hNM]
  have hXa : X a = N := by simp [hX, ha]
  have hXle0 : ∀ k, X k ≤ X 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hXmono k).trans ih
  have hstep : ∀ k < a, ell (X k) (X (k + 1)) ≤
      Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro k hk
    have hD : (N ⊓ F k) ⊔ (M ⊓ F (k + 1)) ≤ X (k + 1) :=
      sup_le (inf_le_left.trans le_sup_left) le_sup_right
    have heq : X (k + 1) ⊔ (M ⊓ F k) = X k := by
      simp only [hX]
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left
          (le_sup_of_le_right (inf_le_inf_left _ (hanti (Nat.le_succ k))))) le_sup_right
      · exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    have h1 : ell (X k) (X (k + 1)) ≤ ell (M ⊓ F k) ((N ⊓ F k) ⊔ (M ⊓ F (k + 1))) := by
      calc ell (X k) (X (k + 1)) = ell (X (k + 1) ⊔ (M ⊓ F k)) (X (k + 1)) := by rw [heq]
        _ ≤ _ := ell_sup_le hD
    exact h1.trans (ell_stepF M N (F k) (F (k + 1)) (φ k) (P k) (Q k) hNM (hinj k) (hP k hk) (hQ k hk))
  have hsum : ∀ j ≤ a, ell (X 0) (X j) ≤
      ∑ k ∈ Finset.range j, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro j
    induction j with
    | zero => intro _; simp [ell, Submodule.comap_subtype_self]
    | succ j ih =>
      intro hj
      rw [ell_add (hXmono j) (hXle0 j), Finset.sum_range_succ, add_comm]
      exact add_le_add (ih (Nat.le_of_succ_le hj)) (hstep j hj)
  have hfin := hsum a le_rfl
  rw [hX0, hXa] at hfin
  exact hfin

theorem filtLen_of_F : PI.FiltLenF → PI.FiltLen := by
  intro hF R W _ _ _ F a hanti h0 ha V _ _ φ hinj M N P Q hNM hP hQ
  refine hF R W F a hanti h0 ha V (fun k => (φ k).comp (F k).subtype)
    (fun k x hx => hinj k x x.2 hx) M N P Q hNM ?_ ?_
  · intro k hk
    rw [Submodule.map_comp, Submodule.map_comap_subtype, inf_comm]
    exact hP k hk
  · intro k hk
    rw [Submodule.map_comp, Submodule.map_comap_subtype, inf_comm]
    exact hQ k hk

end PI.FiltrationLength
