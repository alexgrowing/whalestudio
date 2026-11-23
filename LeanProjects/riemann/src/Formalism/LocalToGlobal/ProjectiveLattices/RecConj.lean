import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  (c : Coeff l)

private theorem rt0_conj_ne_lemma : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h2
  have hre := Complex.conj_eq_iff_re.mp h2
  have hsq := H.sqrt_neg_disc_sq
  rw [← hre] at hsq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h3 : ((H.rt0.re ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ) : ℝ) : ℂ) := by push_cast; exact hsq
  have h4 := Complex.ofReal_injective h3
  nlinarith [sq_nonneg H.rt0.re]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  unfold GoodEmb at h h'
  simp only [RingHom.comp_apply] at h h'
  rw [h] at h'
  exact rt0_conj_ne_lemma h'

private theorem imaginary_root_conj_lemma_2 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
  have h1 : ((starRingEnd ℂ) H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact absurd h rt0_conj_ne_lemma
  · exact h

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have key : ∀ τ : c.F →+* ℂ, GoodEmb c τ ∨ GoodEmb c ((starRingEnd ℂ).comp τ) := by
    intro τ
    unfold GoodEmb
    simp only [RingHom.comp_apply]
    generalize hxd : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = x
    have hx : (x : ℂ) = H.rt0 := by rw [← hxd]; rfl
    have hx2 : x ^ 2 = -((H.d : ℕ) : c.F) := by
      apply Subtype.ext
      have h0 : (x : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := by rw [hx, H.sqrt_neg_disc_sq]
      exact_mod_cast h0
    have hsq : (τ x) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hx2, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · right
      rw [h, map_neg, imaginary_root_conj_lemma_2, neg_neg]
  unfold goodOf
  by_cases h1 : GoodEmb c σ
  · have h2 := not_good_conj c h1
    rw [if_neg h2, if_pos h1]
    ext x
    simp
  · rcases key σ with h | h
    · exact absurd h h1
    · rw [if_pos h, if_neg h1]

end

variable {D : D7} {T : Core D} (h : LawsCore T)

theorem recB_supN_conj (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (F : (recB h).Cusp j w) :
    (recB h).supN j w ((starRingEnd ℂ).comp σ) F = (recB h).supN j w σ F := by
  simp [recB, mkB, cutN, Core.Ns, goodOf_conj]

end Formalism.L2.Pj
