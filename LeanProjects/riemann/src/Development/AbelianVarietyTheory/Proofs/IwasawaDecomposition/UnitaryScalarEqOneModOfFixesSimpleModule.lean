import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSplittingOfCharacter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAddEquivField

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.UnitaryScalarModT

theorem eq_one_add_of_fixes : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : Module.finrank F E = 2) (_ : ∀ x, σ (σ x) = x) (_ : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (_ : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (_ : T.Prime)
    (_ : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (M : Type) [AddCommGroup M] [Module (intV E v) M] (_ : Nat.card M = T) (m : M) (_ : m ≠ 0) (d c : intV E v) (_ : (d - 1) • m = 0)
    (_ : sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F)),
    ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hun v T hT hunif M _ _ hM m hm d c hd hc
  obtain ⟨χ, hχ⟩ := GlobalTheory.PrimeOrderModule.exists_character (intV E v) M T hT hM
  obtain ⟨s, hs, hsχ⟩ := GlobalTheory.OverSplit.exists_splitting_of_character F E σ hdeg hσ hfix hun v T hT χ
  obtain ⟨⟨ε, hε⟩, -, -⟩ := GlobalTheory.OverResidue.residue_of_prime_card F E σ v s hs M T hT hM
    (fun a m ha => hχ a m (hsχ a ha))
  have hεm : ε m ≠ 0 := fun h => hm (ε.injective (h.trans (map_zero ε).symm))
  have key : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = (s a).1 → a • m = 0 →
      a' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro a a' h h0
    have h1 := hε a a' h m
    rw [h0, map_zero] at h1
    have h2 : IsLocalRing.residue _ a' * ε m = 0 := h1.symm
    exact (IsLocalRing.residue_eq_zero_iff _).1 ((mul_eq_zero.1 h2).resolve_right hεm)
  obtain ⟨hd1, hd2⟩ := (hs.2.2 d).1 d.2
  obtain ⟨hc1, -⟩ := (hs.2.2 c).1 c.2
  set d₁ : v.adicCompletionIntegers F := ⟨_, hd1⟩ with hd₁
  set d₂ : v.adicCompletionIntegers F := ⟨_, hd2⟩ with hd₂
  set c₁ : v.adicCompletionIntegers F := ⟨_, hc1⟩ with hc₁
  have m1 : d₁ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (d - 1) _ (by simp [hd₁]) hd
  have mT : (T : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (T : intV E v) _ (by simp) (by rw [Nat.cast_smul_eq_nsmul, ← hM, card_nsmul_eq_zero'])
  have hrel : d₂ * d₁ = 1 + (T : v.adicCompletionIntegers F) * c₁ := by
    have h := congrArg (fun x => (s x).1) hc
    simp only [map_mul, map_add, map_one, map_natCast, hs.2.1] at h
    exact Subtype.ext (by simpa [hd₁, hd₂, hc₁, swapR] using h)
  have m2 : d₂ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : d₂ - 1 = (T : v.adicCompletionIntegers F) * c₁ - d₂ * (d₁ - 1) := by
      linear_combination hrel
    rw [this]
    exact sub_mem (Ideal.mul_mem_right _ _ mT) (Ideal.mul_mem_left _ _ m1)
  obtain ⟨b₁, hb₁⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₁ - 1)).1 m1)
  obtain ⟨b₂, hb₂⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₂ - 1)).1 m2)
  refine ⟨⟨s.symm ((b₁ : v.adicCompletion F), (b₂ : v.adicCompletion F)), (hs.2.2 _).2 ?_⟩, s.injective ?_⟩
  · rw [s.apply_symm_apply]
    exact ⟨b₁.2, b₂.2⟩
  · have e1 : (s d).1 - 1 = (T : v.adicCompletion F) * b₁ := by
      have h := congrArg Subtype.val hb₁
      push_cast at h
      exact h
    have e2 : (s d).2 - 1 = (T : v.adicCompletion F) * b₂ := by
      have h := congrArg Subtype.val hb₂
      push_cast at h
      exact h
    rw [map_add, map_one, map_mul, map_natCast, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using sub_eq_iff_eq_add'.1 e1
    · simpa using sub_eq_iff_eq_add'.1 e2

end GlobalTheory.UnitaryScalarModT
