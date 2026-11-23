import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.IsGalGen

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def ChapterR : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] [IsGalois F E] (l : ℕ), l.Prime → Module.finrank F E = l →
    (∃ η : HChar F, IsGalGen E l η) ∧
    (∀ (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ) (Ps : ∀ i, CG E (m i)),
      1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps) ∧
    ∀ η : HChar F, IsGalGen E l η →
      (∀ (n n' : ℕ) (π : CG F n) (π' : CG F n'), 1 ≤ n → 1 ≤ n' → π.IsUnitary → π'.IsUnitary →
        ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Above S T →
          ∀ (α : Off F S → Fin n → ℂˣ) (β : Off F S → Fin n' → ℂˣ) (A : Off E T → Fin n → ℂˣ)
            (B : Off E T → Fin n' → ℂˣ), SatOff π S α → SatOff π' S β → BCFam α A → BCFam β B →
            ∀ s : ℂ, 2 < s.re → LS T A B s = ∏ k : Fin l, LS S α (fun v b => β v b * η.val v.1 ^ (k : ℕ)) s) ∧
      (∀ (n : ℕ) (π π' : CG F n), 1 ≤ n → SameBC E π π' → ∃ k : ℕ, k < l ∧ π' = π.twist (η ^ k)) ∧
      (∀ (n : ℕ) (π : CG F n) (ι : Type) [Fintype ι] (m : ι → ℕ) (Ps : ∀ i, CG E (m i)),
        1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → IsWL π Ps →
          ∃ k : ℕ, 0 < k ∧ k < l ∧ π = π.twist (η ^ k)) ∧
      (∀ (n : ℕ) (π : CG F n) (P : CG E n), 1 ≤ n → IsWL π (ι := Unit) (m := fun _ => n) (fun _ => P) →
        ∀ k : ℕ, 0 < k → k < l → π ≠ π.twist (η ^ k))

end PositivityTheory.Rg.Tf.ChR
