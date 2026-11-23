import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace CasimirAdjoint

theorem ent {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c d = g c a * g⁻¹ b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul]

private theorem reorder_lemma {ι X : Type} [Fintype ι] [AddCommMonoid X] (G : ι → ι → ι → ι → X) :
    ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w := by
  calc ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ x, ∑ z, ∑ y, ∑ w, G x y z w :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, ∑ w, G x y z w := Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ w, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_comm

theorem reorder {ι X : Type} [Fintype ι] [AddCommMonoid X] (F : ι → ι → ι → ι → ι → ι → X) :
    ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f := by
  calc ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f
        = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          reorder_lemma (fun e f c d => F a b c d e f)
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ e, ∑ f, F a b c d e f :=
        reorder_lemma (fun a b c d => ∑ e, ∑ f, F a b c d e f)
    _ = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          reorder_lemma (fun a b e f => F a b c d e f)

end CasimirAdjoint

open CasimirAdjoint in
theorem casimir_adjoint_holds : CasAd := by
  intro n M _ _ E g hg
  have h : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have key : ∀ c d e f : Fin n, ∑ a, ∑ b, g c a * g⁻¹ b d * (g e b * g⁻¹ a f) =
      (1 : Matrix (Fin n) (Fin n) ℂ) c f * (1 : Matrix (Fin n) (Fin n) ℂ) e d := by
    intro c d e f
    rw [← h, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [actM, casimir, ent, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  refine (reorder (fun a b c d e f => (g c a * g⁻¹ b d * (g e b * g⁻¹ a f)) • (E c d * E e f))).trans ?_
  simp only [← Finset.sum_smul, key, Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
