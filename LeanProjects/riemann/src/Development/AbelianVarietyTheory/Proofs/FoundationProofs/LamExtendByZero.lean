import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

open Classical in

theorem lam_extend_by_zero : ∀ (k L N : ℕ) (χ₀ : DirichletCharacter ℂ N) (B : ℕ) (c : ℕ → ℂ), 0 < L → N ∣ L →
    ∃ (B' : ℕ) (c' : ℕ → ℂ), (∀ a, MF k L (ch χ₀) a → lam B' c' a = lam B c a) ∧
      ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ₀ → MF k L (ch ε) a → lam B' c' a = 0 := by
  intro k L N χ₀ B c hL hN
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k L
  let Fam : (DirichletCharacter ℂ N → ℕ → ℂ) → Prop := fun a => ∀ ε, MF k L (ch ε) (a ε)
  have uniq : ∀ a b, Fam a → Fam b → (∑ ε, a ε) = ∑ ε, b ε → a = b := by
    intro a b ha hb hab
    have hd : Fam (fun ε => a ε + (-1 : ℂ) • b ε) := fun ε =>
      ((lin (ch ε)).2.1 _ _ (ha ε) ((lin (ch ε)).2.2.1 (-1) _ (hb ε)).1).1
    have h0 := GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero k L N (fun ε => a ε + (-1 : ℂ) • b ε) hL hN hd (by
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hab, neg_one_smul, add_neg_cancel])
    funext ε
    have h1 : a ε + (-1 : ℂ) • b ε = 0 := h0 ε
    rw [neg_one_smul, ← sub_eq_add_neg] at h1
    exact sub_eq_zero.mp h1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.sturm_sum_over_characters_eq_zero k L N hL hN
  let S : Set (ℕ → ℂ) := {s | ∃ a, Fam a ∧ s = ∑ ε, a ε}
  let rep : (ℕ → ℂ) → DirichletCharacter ℂ N → ℕ → ℂ := fun s => if h : s ∈ S then Classical.choose h else 0
  have rep_spec : ∀ a, Fam a → rep (∑ ε, a ε) = a := by
    intro a ha
    have hs : (∑ ε, a ε) ∈ S := ⟨a, ha, rfl⟩
    simp only [rep, dif_pos hs]
    have h := Classical.choose_spec hs
    exact uniq _ _ h.1 ha h.2.symm
  let φ : (ℕ → ℂ) → ℂ := fun s => lam B c (rep s χ₀)
  have lam_add : ∀ x y : ℕ → ℂ, lam B c (x + y) = lam B c x + lam B c y := by
    intro x y; simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have lam_smul : ∀ (t : ℂ) (x : ℕ → ℂ), lam B c (t • x) = t * lam B c x := by
    intro t x; simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  obtain ⟨c', hc'⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite S B₀ φ
    ⟨0, fun ε => (lin (ch ε)).1, by simp⟩
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : Fam (a + b) := fun ε => ((lin (ch ε)).2.1 _ _ (ha ε) (hb ε)).1
      have e : (∑ ε, a ε) + ∑ ε, b ε = ∑ ε, (a + b) ε := by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      refine ⟨⟨a + b, hab, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = lam B c (rep _ χ₀) + lam B c (rep _ χ₀)
      rw [e, rep_spec _ hab, rep_spec _ ha, rep_spec _ hb]
      exact lam_add _ _)
    (by
      rintro t _ ⟨a, ha, rfl⟩
      have hta : Fam (t • a) := fun ε => ((lin (ch ε)).2.2.1 t _ (ha ε)).1
      have e : t • ∑ ε, a ε = ∑ ε, (t • a) ε := by
        simp only [Pi.smul_apply, Finset.smul_sum]
      refine ⟨⟨t • a, hta, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = t * lam B c (rep _ χ₀)
      rw [e, rep_spec _ hta, rep_spec _ ha]
      exact lam_smul _ _)
    (by
      rintro _ ⟨a, ha, rfl⟩ h
      exact hB₀ a ha h)
  have single : ∀ (ε₀ : DirichletCharacter ℂ N) (a : ℕ → ℂ), MF k L (ch ε₀) a →
      lam B₀ c' a = lam B c (if ε₀ = χ₀ then a else 0) := by
    intro ε₀ a ha
    let fa : DirichletCharacter ℂ N → ℕ → ℂ := fun ε => if ε = ε₀ then a else 0
    have hfa : Fam fa := by
      intro ε
      by_cases h : ε = ε₀
      · subst h; simp only [fa, if_pos rfl]; exact ha
      · simp only [fa, if_neg h]; exact (lin (ch ε)).1
    have hs : ∑ ε, fa ε = a := by simp [fa]
    have h := hc' _ ⟨fa, hfa, rfl⟩
    simp only [φ] at h
    rw [rep_spec _ hfa, hs] at h
    rw [← h]
    by_cases h' : ε₀ = χ₀
    · subst h'; simp [fa]
    · simp [fa, h', Ne.symm h']
  refine ⟨B₀, c', fun a ha => by simpa using single χ₀ a ha, fun ε a hε ha => ?_⟩
  rw [single ε a ha, if_neg hε]
  simp [lam]

end GlobalTheory
