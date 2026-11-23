import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtReg

theorem exists_ne_of_avg_ne {H : Type} [Group H] {u : H → ℂ} (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [avg, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem exists_ne_of_hint_ne {H : Type} [Group H] {K : Subgroup H} {u : H → ℂ} (h : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [hint, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem charpoly_conj_GL {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (k g : GL ι R) :
    ((k⁻¹ * g * k : GL ι R) : Matrix ι ι R).charpoly = (g : Matrix ι ι R).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem ctMu_regAt2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf m hm
  have hct : ct h w (fun y => f (toSub _ y)) m ≠ 0 := by
    intro h0; apply hm; rw [ctMu, h0, mul_zero]
  rw [ct] at hct
  obtain ⟨X, hX⟩ := exists_ne_of_hint_ne (right_ne_zero_of_mul hct)
  obtain ⟨k, hk⟩ := exists_ne_of_avg_ne hX
  have hsep := hf _ hk
  have hmem : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k) ∈ UL n w := by
    rw [UL, if_pos hw]; exact Subgroup.mem_top _
  have e0 : (toSub (UL n w) ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)).1 =
      (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k := by
    rw [toSub, dif_pos hmem]
  rw [e0, charpoly_conj_GL, blk_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁] at hsep
  have e1 : nrmL a w m.1 = m.1 := by rw [nrmL, if_pos hw]
  have e2 : nrmL b w m.2 = m.2 := by rw [nrmL, if_pos hw]
  rw [e1, e2]
  exact hsep

end GlobalTheory.BCT.CtReg
