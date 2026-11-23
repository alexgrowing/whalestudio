import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

noncomputable section

namespace Tw.RatDarboux
open _root_.GlobalTheory

section General

open scoped TensorProduct
open Matrix Module GlobalTheory.WeilM

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def sympBil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) (JA : Matrix α α S)
    (JB : Matrix β β S) : LinearMap.BilinForm R (Matrix α β S) :=
  LinearMap.mk₂ R (symp c ξ JA JB)
    (fun x x' y => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem exists_darboux_of_basis {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W]
    [Fintype κ] (B : LinearMap.BilinForm R W) (b : Basis (κ ⊕ κ) R W)
    (h11 : ∀ i j, B (b (.inl i)) (b (.inl j)) = 0) (h22 : ∀ i j, B (b (.inr i)) (b (.inr j)) = 0)
    (h12 : ∀ i, B (b (.inl i)) (b (.inr i)) = 1) (h12' : ∀ i j, i ≠ j → B (b (.inl i)) (b (.inr j)) = 0)
    (h21 : ∀ i, B (b (.inr i)) (b (.inl i)) = -1) (h21' : ∀ i j, i ≠ j → B (b (.inr i)) (b (.inl j)) = 0) :
    ∃ co : Darboux (fun x y => B x y) κ,
      ∀ w, co.e w = (fun k => b.repr w (.inl k), fun k => b.repr w (.inr k)) := by
  classical
  have e12 : ∀ i j, B (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0 := fun i j => by
    split_ifs with h
    · subst h; exact h12 i
    · exact h12' i j h
  have e21 : ∀ i j, B (b (.inr i)) (b (.inl j)) = if i = j then -1 else 0 := fun i j => by
    split_ifs with h
    · subst h; exact h21 i
    · exact h21' i j h
  refine ⟨⟨b.equivFun ≪≫ₗ LinearEquiv.sumArrowLequivProdArrow κ κ R R, fun w w' => ?_⟩, fun w => rfl⟩
  show B w w' = (fun k => b.repr w (.inl k)) ⬝ᵥ (fun k => b.repr w' (.inr k)) -
    (fun k => b.repr w' (.inl k)) ⬝ᵥ (fun k => b.repr w (.inr k))
  conv_lhs => rw [← b.sum_repr w, ← b.sum_repr w']
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Fintype.sum_sum_type, map_add,
    LinearMap.add_apply, h11, h22, e12, e21, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero,
    mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, mul_one, mul_neg, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq α] [DecidableEq β] in
theorem sum_four_swap {M : Type} [AddCommMonoid M] (f : α → β → α → β → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
  have h : ∀ g : α → β → α → β → M,
      ∑ i, ∑ j, ∑ k, ∑ l, g i j k l = ∑ p : α × β, ∑ q : α × β, g p.1 p.2 q.1 q.2 := fun g => by
    simp only [Fintype.sum_prod_type]
  rw [h, h fun i j k l => f k l i j, Finset.sum_comm]

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem isAlt_sympBil [CharZero F] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : ∀ i j, σ (JA j i) = JA i j) (hB : ∀ i j, σ (JB j i) = -JB i j) : (sympBil σ (-1) JA JB).IsAlt := by
  intro x
  show Algebra.trace F E (-1 * hTens σ JA JB x x) = 0
  have h : σ (hTens σ JA JB x x) = -hTens σ JA JB x x := by
    simp only [hTens, map_sum, map_mul, hσ, hA, hB]
    simp only [← Finset.sum_neg_distrib]
    rw [sum_four_swap]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  have ht : Algebra.trace F E (σ (hTens σ JA JB x x)) = Algebra.trace F E (hTens σ JA JB x x) :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ (Function.Involutive.bijective hσ)) _
  rw [h, map_neg] at ht
  rw [neg_one_mul, map_neg]
  linear_combination (1 / 2 : F) * ht

theorem bijective_sympBil [CharZero F] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E}
    {JB : Matrix β β E} (hA : JA.det ≠ 0) (hB : JB.det ≠ 0) : Function.Bijective (sympBil σ (-1) JA JB) := by
  have hi : Function.Injective (sympBil σ (-1) JA JB) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : JAᵀ * x * JB = 0 := by
      ext k l
      refine (traceForm_nondegenerate F E).1 _ fun a => ?_
      have := LinearMap.congr_fun hx (Matrix.single k l (σ (-a)))
      change Algebra.trace F E (-1 * hTens σ JA JB x _) = 0 at this
      rw [Algebra.traceForm_apply, ← this]
      congr 1
      have hs : ∀ i j, ∑ k', ∑ l', x i j * JA i k' * JB j l' * σ (Matrix.single k l (σ (-a)) k' l') =
          x i j * JA i k * JB j l * -a := fun i j => by
        rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
        · rw [Matrix.single_apply_same, hσ]
        · intro l' _ h
          rw [Matrix.single_apply_of_col_ne _ _ h.symm, map_zero, mul_zero]
        · simp
        · intro k' _ h
          refine Finset.sum_eq_zero fun l' _ => ?_
          rw [Matrix.single_apply_of_row_ne h.symm, map_zero, mul_zero]
        · simp
      simp only [hTens, hs, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 : x = (JAᵀ)⁻¹ * (JAᵀ * x * JB) * JB⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit hB),
        Matrix.nonsing_inv_mul_cancel_left _ _ (by rw [det_transpose]; exact Ne.isUnit hA)]
    rw [h2, h1, Matrix.mul_zero, Matrix.zero_mul]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

variable (R : Type) [CommRing R] [Algebra F R]

def matBC : R ⊗[F] Matrix α β E ≃ₗ[R] Matrix α β (R ⊗[F] E) :=
  (TensorProduct.piRight F R R (fun _ : α => β → E)) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => TensorProduct.piRight F R R (fun _ : β => E)

theorem matBC_one (x : Matrix α β E) :
    matBC R ((1 : R) ⊗ₜ[F] x) = x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) := by
  ext i j
  rfl

theorem symp_map (σ : E →ₐ[F] E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    symp (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1) (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (y.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) = algebraMap F R (symp σ (-1) JA JB x y) := by
  have ht : ∀ e : E, Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R e) =
      algebraMap F R (Algebra.trace F E e) := fun e => by
    show Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, Algebra.TensorProduct.map (AlgHom.id R R) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (σ e) := fun e => rfl
  rw [symp, symp, ← ht]
  simp only [hTens, Matrix.map_apply, hc, map_mul, map_sum, map_neg, map_one]

theorem exists_darboux [CharZero F] [Invertible (2 : R)] (h2 : finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : ∀ i j, σ (JA j i) = JA i j) (hB : ∀ i j, σ (JB j i) = -JB i j) (hA' : JA.det ≠ 0) (hB' : JB.det ≠ 0) :
    ∃ co : Darboux (symp (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1)
      (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))) (α × β),
      ∀ x : Matrix α β E, ∃ y z : α × β → F, co.e (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) =
        (fun k => algebraMap F R (y k), fun k => algebraMap F R (z k)) := by
  have halt := isAlt_sympBil σ hσ hA hB
  have hrk : finrank F (Matrix α β E) = 2 * Fintype.card (α × β) := by
    rw [Module.finrank_matrix, h2, Fintype.card_prod]; ring
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank halt (bijective_sympBil σ hσ hA' hB') hrk
  let ε := Fintype.equivFin (α × β)
  let b : Basis ((α × β) ⊕ (α × β)) F (Matrix α β E) := b₀.reindex (Equiv.sumCongr ε ε).symm
  have hl : ∀ i, b (.inl i) = b₀ (.inl (ε i)) := fun i => by simp [b]
  have hr : ∀ i, b (.inr i) = b₀ (.inr (ε i)) := fun i => by simp [b]
  let b' := (b.baseChange R).map (matBC R)
  have hb' : ∀ i j, sympBil (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1)
      (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (b' i) (b' j) =
      algebraMap F R (sympBil σ (-1) JA JB (b i) (b j)) := fun i j => by
    simp only [b', Basis.map_apply, Basis.baseChange_apply, matBC_one]
    exact symp_map R σ JA JB _ _
  obtain ⟨co, hco⟩ := exists_darboux_of_basis _ b'
    (fun i j => by rw [hb', hl, hl, GlobalTheory.IsSymplecticFamily.left_left hb₀, map_zero])
    (fun i j => by rw [hb', hr, hr, GlobalTheory.IsSymplecticFamily.right_right hb₀, map_zero])
    (fun i => by rw [hb', hl, hr, GlobalTheory.IsSymplecticFamily.left_right_self hb₀, map_one])
    (fun i j h => by rw [hb', hl, hr, GlobalTheory.IsSymplecticFamily.left_right_ne hb₀ _ _ (ε.injective.ne h), map_zero])
    (fun i => by rw [hb', hl, hr, ← halt.neg_eq, GlobalTheory.IsSymplecticFamily.left_right_self hb₀, map_neg, map_one])
    (fun i j h => by
      rw [hb', hl, hr, ← halt.neg_eq, GlobalTheory.IsSymplecticFamily.left_right_ne hb₀ _ _ (ε.injective.ne h.symm),
        neg_zero, map_zero])
  refine ⟨co, fun x => ⟨fun k => b.repr x (.inl k), fun k => b.repr x (.inr k), ?_⟩⟩
  have hx : ∀ i, b'.repr (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) i = algebraMap F R (b.repr x i) := fun i => by
    rw [← matBC_one]
    simp [b', Algebra.smul_def]
  rw [hco]
  simp only [hx]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) :
    M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hM] at this
  simp at this

end General

end Tw.RatDarboux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory in

theorem Tw.RatDarboux.exists_rational_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hY' : Y.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hY.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det Y.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  exact Tw.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hX.herm hY.skew hX' hY'
