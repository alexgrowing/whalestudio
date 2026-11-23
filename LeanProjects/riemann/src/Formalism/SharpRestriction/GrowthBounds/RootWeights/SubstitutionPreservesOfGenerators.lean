import Formalism.SharpRestriction.GrowthBounds.RootWeights.PropertySubmoduleWeightEntryComponent

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (weightComponent LL S nu F) = if wtS LL S m = nu then coeff m F else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : coeff m F = 0 <;> simp [h1, h2]

theorem sum_weightComponents {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) :
    F = ∑ nu ∈ F.support.image (fun m => wtS LL S m), weightComponent LL S nu F := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_weightComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 hne))

section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W

theorem substitution_preserves_of_generators (h h' : Matrix (Fin n) (Fin n) L)
    (hw : ∀ w ∈ W, matrixSubst LL S φ h h' w ∈ scalarExtension φ W) : SubstitutionPreservesExtension LL S φ W h h' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hwW, rfl⟩ := hy
    have e : matrixSubst LL S (RingHom.id L) h h' (MvPolynomial.map φ w) = matrixSubst LL S φ h h' w := by
      simp only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      rfl
    rw [e]
    exact hw w hwW
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    have e : matrixSubst LL S (RingHom.id L) h h' (MvPolynomial.C c) = MvPolynomial.C c := by
      simp [matrixSubst]
    rw [e, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ c hy

private theorem v1r_act_mul_lemma (h1 h1' h2 h2' : Matrix (Fin n) (Fin n) L) :
    matrixSubst LL S (RingHom.id L) (h1 * h2) (h2' * h1') =
      (matrixSubst LL S (RingHom.id L) h1 h1').comp (matrixSubst LL S (RingHom.id L) h2 h2') := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [matrixSubst]
  · rintro ⟨l, a⟩
    by_cases hl : l ∈ S
    · by_cases hv : LL.vec l = true
      · simp [matrixSubst, hl, hv, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, map_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
        ring
      · simp [matrixSubst, hl, hv, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, map_sum, ← mul_assoc]
        rw [Finset.sum_comm]
    · simp [matrixSubst, hl]

theorem substitution_preserves_mul {h1 h1' h2 h2' : Matrix (Fin n) (Fin n) L} (H1 : SubstitutionPreservesExtension LL S φ W h1 h1')
    (H2 : SubstitutionPreservesExtension LL S φ W h2 h2') : SubstitutionPreservesExtension LL S φ W (h1 * h2) (h2' * h1') := by
  intro x hx
  rw [v1r_act_mul_lemma, RingHom.comp_apply]
  exact H1 _ (H2 x hx)

theorem substitution_preserves_transvection (hT : TransvectionExpansion) (hW : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W)
    (a b : Fin n) (hab : a ≠ b) (t : L) :
    SubstitutionPreservesExtension LL S φ W (Matrix.transvection a b t) (Matrix.transvection a b (-t)) := by
  apply substitution_preserves_of_generators
  intro w hw
  rw [hT R L ι LL n S φ a b hab t w (w.totalDegree + 1) (Nat.lt_succ_self _)]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hW a b k hab w hw, rfl⟩)

theorem substitution_preserves_diagonal (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W)
    (D : Fin n → Lˣ) :
    SubstitutionPreservesExtension LL S φ W (Matrix.diagonal fun a => ((D a : Lˣ) : L)) (Matrix.diagonal fun a => (((D a)⁻¹ : Lˣ) : L)) := by
  apply substitution_preserves_of_generators
  intro w hw
  rw [sum_weightComponents LL S w, map_sum]
  refine Submodule.sum_mem _ fun nu _ => ?_
  have hc : weightComponent LL S nu w ∈ W := hGr R ι LL n S W hW w hw nu
  have key : matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Lˣ) : L))
      (Matrix.diagonal fun a => (((D a)⁻¹ : Lˣ) : L)) (weightComponent LL S nu w) =
      MvPolynomial.C (((∏ a, D a ^ (nu a) : Lˣ) : L)) * MvPolynomial.map φ (weightComponent LL S nu w) := by
    rw [weightComponent, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : wtS LL S m = nu := (Finset.mem_filter.1 hm).2
    rw [hTo R L ι LL n S φ D m, MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, hm', mul_comm]
  rw [key, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hc, rfl⟩)

theorem substitution_preserves_extension_all (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents)
    (hW1 : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W)
    (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W)
    (h h' : Matrix (Fin n) (Fin n) L) (hh : h * h' = 1) : SubstitutionPreservesExtension LL S φ W h h' := by
  have hdet : h.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hh
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  subst hinv
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => SubstitutionPreservesExtension LL S φ W M M⁻¹) h hdet ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ a, D a ≠ 0 := by
      intro a ha
      apply hD
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ a) ha
    have hmul : Matrix.diagonal D * Matrix.diagonal (fun a => (D a)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hD' a)
    show SubstitutionPreservesExtension LL S φ W (Matrix.diagonal D) (Matrix.diagonal D)⁻¹
    rw [Matrix.inv_eq_right_inv hmul]
    have e := substitution_preserves_diagonal LL S φ W hTo hGr hW2 (fun a => Units.mk0 (D a) (hD' a))
    simpa using e
  · intro t
    have hmul : t.toMatrix * Matrix.transvection t.i t.j (-t.c) = 1 := by
      rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection_mul_transvection_same _ _ t.hij,
        add_neg_cancel, Matrix.transvection_zero]
    show SubstitutionPreservesExtension LL S φ W t.toMatrix t.toMatrix⁻¹
    rw [Matrix.inv_eq_right_inv hmul]
    exact substitution_preserves_transvection LL S φ W hT hW1 t.i t.j t.hij t.c
  · intro A B _ _ HA HB
    show SubstitutionPreservesExtension LL S φ W (A * B) (A * B)⁻¹
    rw [Matrix.mul_inv_rev]
    exact substitution_preserves_mul LL S φ W HA HB

theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (MvPolynomial.coeff m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
