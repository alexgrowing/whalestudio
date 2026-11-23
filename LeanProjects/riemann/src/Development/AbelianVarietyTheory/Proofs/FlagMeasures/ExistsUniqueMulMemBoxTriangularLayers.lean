import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem existsUnique_mul_mem_box_of_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  intro M I A B D _ _ _ _ _ ht C Γ Λ₁ F₁ Λ₂ F₂ Λ₃ F₃ hC hC0 hmul hΓC h1 hmulΓ hinv h1Λ h2Λ h3Λ
    h1s h2s h3s hF₁ hF₂ hF₃ q
  classical

  have h0Γ : C 0 ∈ Γ := hC0 ▸ h1
  have z1 : ∀ i, (0 : A) ∈ Λ₁ i := fun i => h1Λ 0 h0Γ i
  have z2 : (0 : B) ∈ Λ₂ := h2Λ 0 h0Γ rfl
  have z3 : (0 : D) ∈ Λ₃ := h3Λ 0 h0Γ rfl rfl

  have layer1 : ∀ s : Finset I, ∀ q, ∃ m ∈ Γ, ∃ w, m * C q = C w ∧ ∀ i ∈ s, w.1 i ∈ F₁ i := by
    intro s
    induction s using Finset.induction_on_max_value ht with
    | empty => exact fun q => ⟨1, h1, q, one_mul _, by simp⟩
    | insert a s has hmax ih =>
      intro q
      obtain ⟨m, hm, w, hmw, hw⟩ := ih q
      obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₁ a (w.1 a)
      obtain ⟨p, hpΓ, hp1⟩ := h1s a b hbΛ
      obtain ⟨w', hw'eq, hw'1, -, -⟩ := hmul p w
      refine ⟨C p * m, hmulΓ _ hpΓ _ hm, w', by rw [mul_assoc, hmw, hw'eq], ?_⟩
      have key : ∀ i, ht i ≤ ht a → w'.1 i = p.1 i + w.1 i := fun i hi =>
        hw'1 i (fun l hl => by
          rw [hp1]; exact Pi.single_eq_of_ne (ne_of_apply_ne ht (by omega)) _)
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [key i le_rfl, hp1, Pi.single_eq_same]; exact hbF
      · have hia : i ≠ a := fun h => has (h ▸ hi)
        rw [key i (hmax i hi), hp1, Pi.single_eq_of_ne hia, zero_add]; exact hw i hi

  have hex : ∃ m ∈ Γ, ∃ u, m * C q = C u ∧ u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ := by
    obtain ⟨m, hm, w, hmw, hw⟩ := layer1 Finset.univ q
    obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₂ w.2.1
    obtain ⟨p, hpΓ, hp1, hp2⟩ := h2s b hbΛ
    obtain ⟨w', hw'eq, hw'1, hw'2, -⟩ := hmul p w
    obtain ⟨d, ⟨hdΛ, hdF⟩, -⟩ := hF₃ w'.2.2
    obtain ⟨w'', hw''eq, hw''1, hw''2, hw''3⟩ := hmul (0, 0, d) w'
    refine ⟨C (0, 0, d) * (C p * m), hmulΓ _ (h3s d hdΛ) _ (hmulΓ _ hpΓ _ hm), w'',
      by rw [mul_assoc, mul_assoc, hmw, hw'eq, hw''eq], ?_⟩
    have e1 : ∀ i, w'.1 i = w.1 i := fun i => by
      rw [hw'1 i (fun l _ => by rw [hp1]; rfl), hp1]; exact zero_add _
    have e1' : ∀ i, w''.1 i = w'.1 i := fun i => by
      rw [hw''1 i (fun l _ => rfl)]; exact zero_add _
    have e2 : w''.2.1 = w'.2.1 := by rw [hw''2 rfl]; exact zero_add _
    refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · exact Set.mem_univ_pi.2 fun i => by
        rw [e1', e1]; exact hw i (Finset.mem_univ i)
    · rw [e2, hw'2 hp1, hp2]; exact hbF
    · rw [hw''3 rfl rfl]; exact hdF

  have rigid : ∀ g ∈ Γ, ∀ u u', u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ →
      u' ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ → g * C u = C u' → g = 1 := by
    intro g hg u u' hu hu' hgu
    obtain ⟨p, rfl⟩ := hΓC hg
    obtain ⟨w, hweq, hw1, hw2, hw3⟩ := hmul p u
    have hwu : w = u' := hC (hweq.symm.trans hgu)
    rw [hwu] at hw1 hw2 hw3
    simp only [Set.mem_prod, Set.mem_univ_pi] at hu hu'

    have key : ∀ n, ∀ i, ht i = n → p.1 i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        have e := hw1 i (fun l hl => ih (ht l) (hi ▸ hl) l rfl)
        exact (hF₁ i (u.1 i)).unique ⟨h1Λ p hg i, e ▸ hu'.1 i⟩ ⟨z1 i, (zero_add (u.1 i)).symm ▸ hu.1 i⟩
    have hp1 : p.1 = 0 := funext fun i => key _ i rfl
    have hp2 : p.2.1 = 0 :=
      (hF₂ u.2.1).unique ⟨h2Λ p hg hp1, hw2 hp1 ▸ hu'.2.1⟩ ⟨z2, (zero_add u.2.1).symm ▸ hu.2.1⟩
    have hp3 : p.2.2 = 0 :=
      (hF₃ u.2.2).unique ⟨h3Λ p hg hp1 hp2, hw3 hp1 hp2 ▸ hu'.2.2⟩
        ⟨z3, (zero_add u.2.2).symm ▸ hu.2.2⟩
    have hp : p = 0 := Prod.ext hp1 (Prod.ext hp2 hp3)
    rw [hp, hC0]

  obtain ⟨m, hmΓ, u, hmu, hu⟩ := hex
  refine ⟨m, ⟨hmΓ, u, hu, hmu.symm⟩, ?_⟩
  rintro m' ⟨hm'Γ, u', hu', hm'u⟩
  obtain ⟨n, hnΓ, hnm⟩ := hinv m hmΓ
  have hg : m' * n = 1 := by
    refine rigid (m' * n) (hmulΓ _ hm'Γ _ hnΓ) u u' hu hu' ?_
    rw [← hmu, hm'u, ← mul_assoc, mul_assoc m', hnm, mul_one]
  calc m' = m' * (n * m) := by rw [hnm, mul_one]
    _ = m' * n * m := (mul_assoc _ _ _).symm
    _ = m := by rw [hg, one_mul]

end GlobalTheory.DegVol.RefCov
