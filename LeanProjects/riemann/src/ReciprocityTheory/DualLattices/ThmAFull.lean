import ReciprocityTheory.DualLattices.OneAddPowOfSq
import ReciprocityTheory.DualLattices.StThmAFull
import ReciprocityTheory.DualLattices.MapSmulOneMulVec

noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

private lemma ev_expand (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, h (gb a) * B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) b := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Algebra.linearMap_apply, Module.Basis.coord_apply]
    conv_lhs => rw [← gb.sum_repr x]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

private lemma stdJ_form {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem thmAFull (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : ThmAFullStatement B Tw := by
  intro _ Dp g gb τ E ht bt hc hEt hdiag hdet hpair hheight hbt
  have h4 := b4 B hB1 hB3 Tw Dp (Fin g ⊕ Fin g) τ E ht bt hpair hheight hbt
  have hJ : (thmAPhi B gb ht bt)ᵀ * stdJ (Tw.O : Type) g * thmAPhi B gb ht bt = Tw.c • E := by
    ext i j
    rw [stdJ_form, Matrix.smul_apply, smul_eq_mul, h4 i j, ev_expand B gb (ht j),
      ev_expand B gb (ht i), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [thmAPhi, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    ring
  exact ⟨hJ, a1 (Tw.O : Type) g E _ Tw.c hEt hdiag hdet hc hJ⟩

end ReciprocityTheory.PGsh
