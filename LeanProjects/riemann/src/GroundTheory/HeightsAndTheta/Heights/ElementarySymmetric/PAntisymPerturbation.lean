import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AntisymPerturbation

variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}

omit [Fintype T] [DecidableEq T] in

theorem rename_mul_eq_or_neg {R : MvPolynomial (T × Fin N) ℝ} {σ ρ : Equiv.Perm (T × Fin N)}
    (hσ : rename σ R = R ∨ rename σ R = -R) (hρ : rename ρ R = R ∨ rename ρ R = -R) :
    rename ⇑(σ * ρ) R = R ∨ rename ⇑(σ * ρ) R = -R := by
  rw [Equiv.Perm.coe_mul, ← rename_rename]
  rcases hρ with h | h
  · rw [h]; exact hσ
  · rw [h, map_neg]
    rcases hσ with h' | h'
    · right; rw [h']
    · left; rw [h', neg_neg]

theorem rename_swap_eq_or_neg {R : MvPolynomial (T × Fin N) ℝ} (hR : R ∈ antisymSpace T N j)
    (τ : T) (a c : Fin N) (hac : a.val ≤ c.val) (hblk : c.val < j ∨ j ≤ a.val) :
    rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R := by
  have hR' : ∀ σ, IsBlockSimpleSwap T N j σ → rename σ R = -R := hR.2
  suffices H : ∀ k : ℕ, ∀ c : Fin N, c.val = a.val + k → (c.val < j ∨ j ≤ a.val) →
      rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R from
    H (c.val - a.val) c (by omega) hblk
  intro k
  induction k with
  | zero =>
    intro c hc _
    have hca : c = a := Fin.ext (by omega)
    subst hca
    left
    rw [Equiv.swap_self, Equiv.coe_refl, rename_id_apply]
  | succ k ih =>
    intro c hc hb
    have hc' : a.val + k < N := by omega
    have hsimple : rename ⇑(Equiv.swap (τ, (⟨a.val + k, hc'⟩ : Fin N)) (τ, c)) R = -R :=
      hR' _ ⟨τ, ⟨a.val + k, hc'⟩, c, by simp only; omega, by simp only; omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hca : (⟨a.val + 0, hc'⟩ : Fin N) = a := Fin.ext (by simp)
      rw [hca] at hsimple
      exact Or.inr hsimple
    · have hprev := ih ⟨a.val + k, hc'⟩ rfl (by simp only; omega)
      have h1 : (τ, a) ≠ (τ, (⟨a.val + k, hc'⟩ : Fin N)) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have h2 : (τ, a) ≠ (τ, c) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have e := Equiv.swap_mul_swap_mul_swap h1 h2
      rw [Equiv.swap_comm (τ, c) (τ, a)] at e
      rw [← e]
      exact rename_mul_eq_or_neg (rename_mul_eq_or_neg (Or.inr hsimple) hprev) (Or.inr hsimple)

omit [Fintype T] [DecidableEq T] in

theorem image_comp_perm (σ : Equiv.Perm (T × Fin N)) (τ : T) {a b a' b' : Fin N}
    (hσa : σ (τ, a) = (τ, a')) (hσb : σ (τ, b) = (τ, b')) {K : Set (T × Fin N → ℝ)}
    (hKc : IsCompact K) (hKH : K ⊆ diagHyperplane T N τ a' b')
    (hKO : ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a' b').Nonempty ∧
      O ∩ diagHyperplane T N τ a' b' ⊆ K) :
    IsCompact ((fun y => y ∘ ⇑σ) '' K) ∧ (fun y => y ∘ ⇑σ) '' K ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ (fun y => y ∘ ⇑σ) '' K := by
  have hinv_a : σ⁻¹ (τ, a') = (τ, a) := by rw [← hσa]; simp
  have hinv_b : σ⁻¹ (τ, b') = (τ, b) := by rw [← hσb]; simp
  refine ⟨hKc.image (continuous_pi fun p => continuous_apply _), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show y (σ (τ, a)) = y (σ (τ, b))
    rw [hσa, hσb]
    exact hKH hy
  · obtain ⟨O, hO, ⟨y0, hy0O, hy0H⟩, hOK⟩ := hKO
    refine ⟨(fun x => x ∘ ⇑σ⁻¹) ⁻¹' O, hO.preimage (continuous_pi fun p => continuous_apply _),
      ⟨y0 ∘ ⇑σ, ?_, ?_⟩, ?_⟩
    · have e : (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ = y0 := by funext p; simp
      show (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ ∈ O
      rw [e]
      exact hy0O
    · show y0 (σ (τ, a)) = y0 (σ (τ, b))
      rw [hσa, hσb]
      exact hy0H
    · rintro x ⟨hxO, hxH⟩
      refine ⟨x ∘ ⇑σ⁻¹, hOK ⟨hxO, ?_⟩, ?_⟩
      · show x (σ⁻¹ (τ, a')) = x (σ⁻¹ (τ, b'))
        rw [hinv_a, hinv_b]
        exact hxH
      · funext p; simp

end AntisymPerturbation

theorem AntisymPerturbation.proof (hStab : AntisymStability.Statement) :
    AntisymPerturbation.Statement := by
  intro T _ _ N j hj hjN h K hK
  let jm : Fin N := ⟨j - 1, by omega⟩
  let jp : Fin N := ⟨j, hjN⟩
  let σ : T → Fin N → Fin N → Equiv.Perm (T × Fin N) := fun τ a b =>
    Equiv.swap (τ, a) (τ, jm) * Equiv.swap (τ, b) (τ, jp)
  have hσa : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, a) = (τ, jm) := by
    intro τ a b ha hb
    have e1 : Equiv.swap (τ, b) (τ, jp) (τ, a) = (τ, a) := Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [e1, Equiv.swap_apply_left]
  have hσb : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, b) = (τ, jp) := by
    intro τ a b ha hb
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp, jm]; omega)
  have hsign : ∀ R ∈ antisymSpace T N j, ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      rename ⇑(σ τ a b) R = R ∨ rename ⇑(σ τ a b) R = -R := by
    intro R hR τ a b ha hb
    refine AntisymPerturbation.rename_mul_eq_or_neg
      (AntisymPerturbation.rename_swap_eq_or_neg hR τ a jm (by simp only [jm]; omega)
        (Or.inl (by simp only [jm]; omega))) ?_
    rw [Equiv.swap_comm]
    exact AntisymPerturbation.rename_swap_eq_or_neg hR τ jp b (by simp only [jp]; omega)
      (Or.inr (by simp only [jp]; omega))
  obtain ⟨C, hC⟩ := hStab T N j (fun τ a b => (fun y => y ∘ ⇑(σ τ a b)) '' K τ)
    (fun τ a b ha hb => AntisymPerturbation.image_comp_perm (σ τ a b) τ (hσa τ a b ha hb)
      (hσb τ a b ha hb) (hK τ).1 (hK τ).2.1 (hK τ).2.2.1)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ0⟩⟩
  · refine ⟨0, fun P v ε hR _ => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    exact ⟨l, hl, fun m => by simpa using hb 0 le_rfl (fun τ => isEmptyElim τ) m⟩
  · refine ⟨C, fun P v ε hR hε => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    refine ⟨l, hl, hb ε ?_ ?_⟩
    · obtain ⟨O, _, ⟨y, hyO, hyH⟩, hOK⟩ := (hK τ0).2.2.1
      exact (abs_nonneg _).trans (hε τ0 y (hOK ⟨hyO, hyH⟩))
    · rintro τ a b ha hb x ⟨y, hy, rfl⟩
      have hyh : eval y h = 0 := (hK τ).2.2.2 y hy
      have hyP := hε τ y hy
      show |eval (y ∘ ⇑(σ τ a b)) (P - v • h)| ≤ ε
      rw [← eval_rename]
      rcases hsign _ hR τ a b ha hb with e | e
      · rw [e]; simpa [hyh] using hyP
      · rw [e, map_neg, abs_neg]; simpa [hyh] using hyP

end GroundTheory.Heights₂.Heights
