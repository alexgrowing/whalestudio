import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Pin1b

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem pin1 (hx : (U.X k).IsOrtho x.1) (a' : (W.F.Di (W.ik k)).La) :
    A.φ ((W.φ k a' : (U.X k).Λ) : Fin r → E) = Lmap hU hσ W A (star (W.Pm a')) := by
  obtain ⟨v, hv⟩ : ∃ v : Fin r → E, v = ((W.φ k a' : (U.X k).Λ) : Fin r → E) := ⟨_, rfl⟩
  rw [← hv]
  have hdet : ∀ τ : (U.X k).Ψ, (mat x.1 τ).det ≠ 0 := fun τ => (x.2 τ).1
  have hrel : ∀ ρ : E →+* ℂ, relab c σ ((relabE c σ).symm (conjEmb ρ)) = conjEmb ρ :=
    fun ρ => (relabE c σ).apply_symm_apply _
  ext ⟨ρ, a⟩
  rw [Lmap_apply, Pi.star_apply, W.pm_eq, letT_e, ← hv]
  simp only [hrel]
  rw [fibE_val]
  by_cases h : ρ ∈ (U.X k).Ψ
  · rw [if_pos h]
    have ha := index_lt_signature_of_mem hU A h a
    rw [perFr_conj (U.X k) x.1 v h _ (by omega)]
    have e1 := A.coord_pos ⟨ρ, h⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet]
    rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right, wt, dif_pos h, star_def,
      ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj ρ (U.X k).Gm (U.X k).Gm_herm]
    have hidx : (⟨(U.X k).p0 - 1 - ((U.X k).p0 - 1 - (a : ℕ)), by have := (U.X k).p0_le; omega⟩ : Fin r) =
        Fin.castLE (by rw [A.dim_pos ⟨ρ, h⟩]; exact (U.X k).p0_le) a := Fin.ext (by simp; omega)
    rw [hidx]
    have hcast : ∀ (h1 : A.T.dim ρ ≤ r), Fin.castLE h1 a = ⟨a, lt_of_lt_of_le a.2 h1⟩ := fun _ => rfl
    simp only [yf, hcast]
    ring
  · rw [if_neg h]
    obtain ⟨τ, rfl⟩ : ∃ τ, conjEmb τ = ρ := ⟨conjEmb ρ, conjEmb_conjEmb ρ⟩
    have hτ : conjEmb (conjEmb τ) ∈ (U.X k).Ψ := (conj_mem_iff _).mpr h
    have hτ' : τ ∈ (U.X k).Ψ := by rwa [conjEmb_conjEmb] at hτ
    have ha := index_lt_complementSignature_of_not_mem hU A h a
    have hp := (U.X k).p0_le
    rw [perFr_self (U.X k) x.1 v hτ a (by omega), inv_coord (U.X k) x.1 hx _ (hdet _) (Data.emb _ v), wt, dif_neg h]
    have hsub : (⟨conjEmb (conjEmb τ), hτ⟩ : (U.X k).Ψ) = ⟨τ, hτ'⟩ := Subtype.ext (conjEmb_conjEmb τ)
    simp only [hsub]
    rw [conjEmb_conjEmb]
    have e1 := A.coord_neg ⟨τ, hτ'⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet, ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right]
    have hs : (sgn (U.X k).p0 ((U.X k).p0 + (a : ℕ)) : ℂ) = -1 := by
      unfold sgn
      rw [if_neg (by omega)]
      norm_num
    simp only [yf, star_def, map_neg, map_mul, Complex.conj_conj, hs, map_one]
    ring

end Pin1b

end ReciprocityTheory.ChartRestriction.G.PullbackSections
