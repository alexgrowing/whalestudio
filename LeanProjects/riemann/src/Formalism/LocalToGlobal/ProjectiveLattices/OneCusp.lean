import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open scoped ComplexConjugate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem not_isIso_of_p0_zero (X : Data E r) (h0 : X.p0 = 0) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hh, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  obtain ⟨P, hP, hG⟩ := X.signature ⟨τ, hτ⟩
  set v : Fin r → ℂ := fun a => τ (ξ a) with hv
  set w : Fin r → ℂ := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have h1 : hermC τ X.Gm v v = 0 := by
    have := congrArg τ hh
    rw [map_zero] at this
    rw [← this]
    simp only [hermC, herm, map_sum, map_mul, hv, cc, IsCMField.complexEmbedding_complexConj]
  have h2 : hermC τ X.Gm v v = ∑ a, ∑ b, w a * gram τ X.Gm P a b * conj (w b) := by
    have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
        ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := fun f =>
      calc ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ x, ∑ a, ∑ y, ∑ b, f x y a b :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y, ∑ b, f x y a b := Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ b, ∑ y, f x y a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have L : ∀ x y, P.mulVec w x * τ (X.Gm x y) * conj (P.mulVec w y) =
        ∑ a, ∑ b, w a * (P x a * τ (X.Gm x y) * conj (P y b)) * conj (w b) := by
      intro x y
      simp only [Matrix.mulVec, dotProduct]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    rw [← hPw]
    simp only [hermC, L, gram, col, Matrix.of_apply]
    rw [sw]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : ∑ a, Complex.normSq (w a) = 0 := by
    rw [h2, hG] at h1
    have : ∑ a, (Complex.normSq (w a) : ℂ) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb.symm]) (by simp)]
      simp [sgn, h0, Complex.mul_conj]
    exact_mod_cast this
  have h4 : w = 0 := funext fun a => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg _).mp h3 a (Finset.mem_univ a))
  apply hne
  funext a
  have : v a = 0 := by rw [← hPw, h4, Matrix.mulVec_zero]; rfl
  exact (map_eq_zero τ).mp this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩

end

variable {D : D7} {T : Core D}

end Formalism.L2.Pj
