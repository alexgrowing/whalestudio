import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGeneratorsStatement

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem bmon_mul_mem_nfSpan_of_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {c : A} (hc : c ∈ bmon d)
    {x : A} (hx : x ∈ nfSpan d T i j n) : c * x ∈ nfSpan d T i j n := by
  unfold nfSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    have e : c * y = (c * b) * d.L.Di ^ i * TL.gI d.L ^ j * H.prod := by
      rw [hrest]; simp only [mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨c * b, mul_mem hc hb, H, hHl, hH, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy

theorem nfSpan_one_mul_mem_of_letters (d : Q.NFData P A) (T : Set A) {c : A}
    (hc : ∀ X ∈ T, X * c ∈ nfSpan d T 0 0 1) {x : A} (hx : x ∈ nfSpan d T 0 0 1) :
    x * c ∈ nfSpan d T 0 0 1 := by
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    rcases H with _ | ⟨h, _ | ⟨h', t⟩⟩
    · simp at hHl
    · have hhT : h ∈ T := hH h (by simp)
      have e : y * c = b * (h * c) := by
        rw [hrest]; simp [mul_assoc]
      rw [e]
      exact bmon_mul_mem_nfSpan_of_mem d T 0 0 1 hb (hc h hhT)
    · simp at hHl
  | zero => simp
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hy

end

theorem hats_mul_bmon_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d hd X hX b hb
  have key : ∀ X ∈ hats d.L, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
    clear hX X
    unfold bmon at hb
    induction hb using Submonoid.closure_induction with
    | mem b hb =>
      intro X hX
      rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).2
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).2
    | one =>
      intro X hX
      exact Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩
    | mul b₁ b₂ _ _ h₁ h₂ =>
      intro X hX
      rw [← mul_assoc]
      exact nfSpan_one_mul_mem_of_letters d _ h₂ (h₁ X hX)
  exact key X hX

end GlobalTheory.HatNF
