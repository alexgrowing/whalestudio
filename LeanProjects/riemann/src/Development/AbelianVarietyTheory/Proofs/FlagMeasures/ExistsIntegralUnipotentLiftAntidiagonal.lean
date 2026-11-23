import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem exists_lift_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a l hl
  obtain ⟨c, hc, hσ, hlw⟩ := hl
  have hσ' : σ c = -c := hσ
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a 0 c ?_ ?_ ?_ hc
    · intro b _
      simp [form]
    · simp [form, hσ']
    · intro b _
      simp
  have hE : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c) w i j =
      (if i = j then 1 else 0) +
        (if j = esI k r a then (if i = eI k r a then (s a : ℂ) * ((s a : ℂ) * w.embedding c) else 0) else 0) := by
    intro w i j
    have h0 : (A w *ᵥ fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
      have h1 : (fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
        funext l
        simp
      rw [h1, mulVec_zero]
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a 0 c w i j, h0]
    simp [herm]
  have hne : ∀ b b' : Fin r, eI k r b ≠ esI k r b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [eI, esI] at this
    omega
  have hnw : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, esI] at this
    omega
  have hnw' : ∀ (j : Fin (k + 1)) (b : Fin r), eI k r b ≠ wI k r j := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, eI] at this
    omega
  have hee : ∀ b b' : Fin r, b ≠ b' → eI k r b ≠ eI k r b' := by
    intro b b' hb h
    apply hb
    have := congrArg Fin.val h
    simp only [eI] at this
    exact Fin.ext this
  have hss : ∀ b b' : Fin r, esI k r b = esI k r b' → b = b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [esI] at this
    exact Fin.ext (by omega)
  constructor
  · intro w
    show ((gM A _ w) (eI k r a) (esI k r a)).im = l w
    rw [hE, hlw w]
    simp [hne a a, pow_two, mul_assoc, Complex.mul_im]
  · rintro (p | b | p | b) hβ _ w
    · show (gM A _ w) (eI k r p.1.1) (eI k r p.1.2) = 0
      rw [hE]
      have h1 : eI k r p.1.1 ≠ eI k r p.1.2 := hee _ _ (ne_of_lt p.2)
      simp [h1, (hne p.1.2 a)]
    · funext j
      show (gM A _ w) (eI k r b) (wI k r j) = 0
      rw [hE]
      simp [hnw' j b, hnw j a]
    · show (gM A _ w) (eI k r p.1.1) (esI k r p.1.2) = 0
      rw [hE]
      have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      by_cases h2 : p.1.2 = a
      · have h3 : eI k r p.1.1 ≠ eI k r a := hee _ _ (h2 ▸ h1)
        simp [hne p.1.1 p.1.2, h3]
      · have h3 : esI k r p.1.2 ≠ esI k r a := fun h => h2 (hss _ _ h)
        simp [hne p.1.1 p.1.2, h3]
    · show ((gM A _ w) (eI k r b) (esI k r b)).im = 0
      rw [hE]
      have hb : b ≠ a := fun h => hβ (by rw [h])
      have h3 : esI k r b ≠ esI k r a := fun h => hb (hss _ _ h)
      simp [hne b b, h3]

end GlobalTheory.SnMass.VolN
