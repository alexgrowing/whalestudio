import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

namespace GlobalTheory.TamOneInert

theorem map_mk_eq_one_iff {R : Type} [CommRing R] (I : Ideal R) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    M.map (Ideal.Quotient.mk I) = 1 ↔ ∀ a b, (M - 1) a b ∈ I := by
  constructor
  · intro h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub]
    have := congrFun (congrFun h a) b
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  · intro h
    ext a b
    have := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), Set.ncard ((fun g : Matrix (Fin r) (Fin r) (𝓞 E) => g.map (Ideal.Quotient.mk (v.asIdeal.map (algebraMap _ (𝓞 E))))) '' {g | g.det - 1 ∈ v.asIdeal.map (algebraMap _ (𝓞 E)) ∧ ∀ a b, (gᵀ * g.map (IsCMField.ringOfIntegersComplexConj E) - 1) a b ∈ v.asIdeal.map (algebraMap _ (𝓞 E))}) = Nat.card (suMat (𝓞 E ⧸ extIdeal v) (resConj v) r) := by
  intro E _ _ _ r v
  rw [← Nat.card_coe_set_eq]
  congr 2
  have hconj : ∀ g : Matrix (Fin r) (Fin r) (𝓞 E),
      (g.map (Ideal.Quotient.mk (extIdeal v))).map (resConj v) =
        (g.map (IsCMField.ringOfIntegersComplexConj E)).map (Ideal.Quotient.mk (extIdeal v)) := by
    intro g; ext a b; simp [resConj_mk]
  have hdet : ∀ g : Matrix (Fin r) (Fin r) (𝓞 E),
      (g.map (Ideal.Quotient.mk (extIdeal v))).det = Ideal.Quotient.mk (extIdeal v) g.det := by
    intro g; rw [RingHom.map_det]; rfl
  have hkey : ∀ g : Matrix (Fin r) (Fin r) (𝓞 E),
      g.map (Ideal.Quotient.mk (extIdeal v)) ∈ suMat (𝓞 E ⧸ extIdeal v) (resConj v) r ↔
        (g.det - 1 ∈ extIdeal v ∧ ∀ a b, (gᵀ * g.map (IsCMField.ringOfIntegersComplexConj E) - 1) a b ∈ extIdeal v) := by
    intro g
    rw [← map_mk_eq_one_iff]
    simp only [suMat, Set.mem_setOf_eq]
    rw [hconj, hdet, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    have ht : (gᵀ * g.map (IsCMField.ringOfIntegersComplexConj E)).map (Ideal.Quotient.mk (extIdeal v)) =
        (((g.map (IsCMField.ringOfIntegersComplexConj E)).map (Ideal.Quotient.mk (extIdeal v)))ᵀ *
          g.map (Ideal.Quotient.mk (extIdeal v)))ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map]
    rw [ht, Matrix.transpose_eq_one]
    exact and_comm
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hkey g).2 hg
  · intro hx
    obtain ⟨g, rfl⟩ : ∃ g : Matrix (Fin r) (Fin r) (𝓞 E), g.map (Ideal.Quotient.mk (extIdeal v)) = x :=
      ⟨fun a b => (Ideal.Quotient.mk_surjective (x a b)).choose,
        by ext a b; exact (Ideal.Quotient.mk_surjective (x a b)).choose_spec⟩
    exact ⟨g, (hkey g).1 hx, rfl⟩

end GlobalTheory.TamOneInert
