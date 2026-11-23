import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpanStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactorsStatement

namespace GlobalTheory.HatNF.SpanMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem gen_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) (H : List A)
    (hl : H.length = n) (hT : ∀ h ∈ H, h ∈ T) :
    b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod ∈ nfSpan d T i j n :=
  Submodule.subset_span ⟨b, hb, H, hl, hT, rfl⟩

theorem map_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) (f : A →ₗ[ℂ] A) (S : Submodule ℂ A)
    (h : ∀ b ∈ bmon d, ∀ H : List A, H.length = n → (∀ h ∈ H, h ∈ T) →
      f (b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod) ∈ S) :
    ∀ x ∈ nfSpan d T i j n, f x ∈ S := by
  have : nfSpan d T i j n ≤ S.comap f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hl, hT, rfl⟩
    exact h b hb H hl hT
  exact fun x hx => this hx

theorem bdd_mul (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) :
    ∀ x ∈ nfSpan d T i j n, b * x ∈ nfSpan d T i j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ b) _ ?_
  intro b' hb' H hl hT
  have := gen_mem d T i j n ((bmon d).mul_mem hb hb') H hl hT
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di * x ∈ nfSpan d T (i + 1) j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ d.L.Di) _ ?_
  intro b hb H hl hT
  have := gen_mem d T (i + 1) j n hb H hl hT
  rw [pow_succ', ← mul_assoc b, (hD b hb).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem gi_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L * x ∈ nfSpan d T i (j + 1) n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ (TL.gI d.L)) _ ?_
  intro b hb H hl hT
  have := gen_mem d T i (j + 1) n hb H hl hT
  rw [pow_succ', ← mul_assoc (b * _), ((hG b hb).mul_left (hDG.pow_left i)).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_pow_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di ^ k * x ∈ nfSpan d T (i + k) j n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact di_mul d hD T _ j n _ ih

theorem gi_pow_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L ^ k * x ∈ nfSpan d T i (j + k) n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact gi_mul d hG hDG T i _ n _ ih

theorem one_letter_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di)
    (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L)) (hDG : Commute d.L.Di (TL.gI d.L)) (T T' : Set A)
    (i₀ j₀ n i j : ℕ) (u : A) (hu : ∀ X ∈ T', X * u ∈ nfSpan d T i₀ j₀ n) :
    ∀ x ∈ nfSpan d T' i j 1, x * u ∈ nfSpan d T (i₀ + i) (j₀ + j) n := by
  refine map_mem d T' i j 1 (LinearMap.mulRight ℂ u) _ ?_
  intro b hb H hl hT
  obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
  have := bdd_mul d T _ _ n hb _ (di_pow_mul d hD T _ _ n i _
    (gi_pow_mul d hG hDG T _ _ n j _ (hu X (hT X (by simp)))))
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_cons, List.prod_nil, mul_one] using this

theorem mul_prod (d : Q.NFData P A) (T : Set A) (i j m : ℕ) (H : List A) (hT : ∀ h ∈ H, h ∈ T) :
    ∀ x ∈ nfSpan d T i j m, x * H.prod ∈ nfSpan d T i j (H.length + m) := by
  refine map_mem d T i j m (LinearMap.mulRight ℂ H.prod) _ ?_
  intro b hb H' hl hT'
  have := gen_mem d T i j (H.length + m) hb (H' ++ H) (by simp [hl, add_comm]) (by
    intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · exact hT' h h1
    · exact hT h h1)
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_append] using this

theorem span_mul : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  intro P A _ _ _ _ d hd T
  have h1 := GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan P A d hd
  obtain ⟨h2, h3, hDG⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd
  have hD : ∀ b ∈ bmon d, Commute b d.L.Di := fun b hb => (h3 b hb).2.1
  have hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L) := fun b hb => (h3 b hb).2.2.1
  refine ⟨fun i j n x hx => ⟨fun b hb => bdd_mul d T i j n hb x hx, di_mul d hD T i j n x hx,
    gi_mul d hG hDG T i j n x hx⟩, ?_⟩
  intro a ha i j n X hX
  refine map_mem d T i j n (LinearMap.mulLeft ℂ X) _ ?_
  intro b hb H hl hT
  have e1 : ∀ k, X * b * d.L.Di ^ k ∈ nfSpan d (hats d.L) k 0 1 := by
    intro k
    induction k with
    | zero => simpa using h1 X hX b hb
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 1 0 1 k 0 _ (fun Y hY => (h2 Y hY).1) _ ih
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e2 : ∀ k, X * b * d.L.Di ^ i * TL.gI d.L ^ k ∈ nfSpan d (hats d.L) i k 1 := by
    intro k
    induction k with
    | zero => simpa using e1 i
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 0 1 1 i k _ (fun Y hY => (h2 Y hY).2) _ ih
      rw [zero_add] at this
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e3 := one_letter_mul d hD hG hDG T _ 0 a (H.length + 1) i j H.prod
    (fun Y hY => mul_prod d T 0 a 1 H hT Y (ha Y hY)) _ (e2 j)
  rw [zero_add, hl, add_comm a j] at e3
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using e3

end GlobalTheory.HatNF.SpanMul
