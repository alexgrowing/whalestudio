import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

namespace GlobalTheory.CyclotomicQExpansion
open GlobalTheory.KZ

theorem exp_sl_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have hdet : 0 < ent g 0 0 * ent g 1 1 := by
    have h := g.2
    have h' : 0 < Matrix.det ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := h
    rw [Matrix.det_fin_two] at h'
    simp only [ent] at hg ⊢
    rw [hg, mul_zero, sub_zero] at h'
    exact h'
  have hd : ent g 1 1 ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hdet; exact lt_irrefl _ hdet
  have ha : ent g 0 0 ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hdet; exact lt_irrefl _ hdet
  have hpos : 0 < ent g 0 0 / ent g 1 1 := by
    have : ent g 0 0 / ent g 1 1 = (ent g 0 0 * ent g 1 1) / (ent g 1 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hdet (by positivity)
  ext s
  unfold sub scale
  rw [dif_pos hpos]
  set e := (OrderIso.mulLeft₀ (ent g 0 0 / ent g 1 1) hpos).toOrderEmbedding with he
  have hs : s = e (s * ent g 1 1 / ent g 0 0) := by
    simp only [he, RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  rw [hs, HahnSeries.embDomain_coeff]
  have key := X.exp_upper g hg f (s * ent g 1 1 / ent g 0 0)
  have h2 : s * ent g 1 1 / ent g 0 0 * ent g 0 0 / ent g 1 1 = e (s * ent g 1 1 / ent g 0 0) := by
    rw [← hs]; field_simp
  rw [h2] at key
  rw [key]
  rfl

end GlobalTheory.CyclotomicQExpansion
