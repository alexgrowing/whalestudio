import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

noncomputable section

namespace GlobalTheory.RatDarboux

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
  refine ⟨⟨b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite R R (κ ⊕ κ) ≪≫ₗ
    LinearEquiv.sumArrowLequivProdArrow κ κ R R, fun w w' => ?_⟩, fun w => rfl⟩
  have e12 : ∀ i j, B (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact h12 i
    · exact h12' i j h
  have e21 : ∀ i j, B (b (.inr i)) (b (.inl j)) = if i = j then -1 else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact h21 i
    · exact h21' i j h
  have key : B w w' = ∑ p, ∑ q, b.repr w p * b.repr w' q * B (b p) (b q) := by
    conv_lhs => rw [← b.sum_repr w, ← b.sum_repr w']
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  show _ = (∑ k, b.repr w (.inl k) * b.repr w' (.inr k)) - ∑ k, b.repr w' (.inl k) * b.repr w (.inr k)
  rw [key]
  simp only [Fintype.sum_sum_type, h11, h22, e12, e21, mul_zero, Finset.sum_const_zero, zero_add, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq α] [DecidableEq β] in
theorem sum_four_swap {M : Type} [AddCommMonoid M] (f : α → β → α → β → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
  have h1 : ∀ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ j, f i j k l := fun i => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem isAlt_sympBil [CharZero F] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : ∀ i j, σ (JA j i) = JA i j) (hB : ∀ i j, σ (JB j i) = -JB i j) : (sympBil σ (-1) JA JB).IsAlt := by
  intro x
  have hinv : ∀ z : E, Algebra.trace F E (σ z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun y => hσ y) (AlgHom.ext fun y => hσ y)) z
  have hanti : σ (hTens σ JA JB x x) = -hTens σ JA JB x x := by
    simp only [hTens, map_sum, map_mul, hσ]
    rw [sum_four_swap, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA, hB]
    ring
  have ht : Algebra.trace F E (hTens σ JA JB x x) = 0 := by
    have h := hinv (hTens σ JA JB x x)
    rw [hanti, map_neg] at h
    have h2 : (2 : F) * Algebra.trace F E (hTens σ JA JB x x) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  show Algebra.trace F E (-1 * hTens σ JA JB x x) = 0
  rw [neg_one_mul, map_neg, ht, neg_zero]

private theorem hTens_single (σ : E →ₐ[F] E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E)
    (k₀ : α) (l₀ : β) (c : E) :
    hTens σ JA JB x (Matrix.single k₀ l₀ c) = (JAᵀ * x * JB) k₀ l₀ * σ c := by
  have h1 : hTens σ JA JB x (Matrix.single k₀ l₀ c) = ∑ i, ∑ j, x i j * JA i k₀ * JB j l₀ * σ c := by
    unfold hTens
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k₀, Finset.sum_eq_single l₀]
    · simp
    · intro l _ hl
      simp [Matrix.single_apply, Ne.symm hl]
    · simp
    · intro k _ hk
      refine Finset.sum_eq_zero fun l _ => ?_
      simp [Matrix.single_apply, Ne.symm hk]
    · simp
  rw [h1, Matrix.mul_apply, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_apply]
  ring

theorem bijective_sympBil [CharZero F] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E}
    {JB : Matrix β β E} (hA : JA.det ≠ 0) (hB : JB.det ≠ 0) : Function.Bijective (sympBil σ (-1) JA JB) := by
  classical
  have hx0 : ∀ x : Matrix α β E, (∀ y, symp σ (-1) JA JB x y = 0) → x = 0 := by
    intro x hx
    have hN : JAᵀ * x * JB = 0 := by
      ext k₀ l₀
      have ht : ∀ e : E, Algebra.traceForm F E ((JAᵀ * x * JB) k₀ l₀) e = 0 := by
        intro e
        have h := hx (Matrix.single k₀ l₀ (σ e))
        rw [symp, hTens_single, hσ, neg_one_mul, map_neg, neg_eq_zero] at h
        simpa [Algebra.traceForm_apply] using h
      simpa using (traceForm_nondegenerate F E).1 _ ht
    have hAu : IsUnit JAᵀ.det := by
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.2 hA
    have hBu : IsUnit JB.det := isUnit_iff_ne_zero.2 hB
    have h1 : x * JB = 0 := by
      have h := congrArg (fun M => JAᵀ⁻¹ * M) hN
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu] using h
    have h := congrArg (fun M => M * JB⁻¹) h1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu] using h
  have hinj : Function.Injective (sympBil σ (-1) JA JB) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact hx0 x fun y => LinearMap.congr_fun hx y
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj⟩

variable (R : Type) [CommRing R] [Algebra F R]

def matBC : R ⊗[F] Matrix α β E ≃ₗ[R] Matrix α β (R ⊗[F] E) :=
  (TensorProduct.piRight F R R (fun _ : α => β → E)) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => TensorProduct.piRight F R R (fun _ : β => E)

theorem matBC_one (x : Matrix α β E) :
    matBC R ((1 : R) ⊗ₜ[F] x) = x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) := by
  ext i j
  change (TensorProduct.piRight F R R (fun _ : β => E))
    ((TensorProduct.piRight F R R (fun _ : α => β → E)) ((1 : R) ⊗ₜ[F] x) i) j = _
  simp only [TensorProduct.piRight_apply, Matrix.map_apply, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [TensorProduct.piRightHom_tmul]
  rfl

private theorem trace_inclR_divisor (z : E) :
    Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R z) =
      algebraMap F R (Algebra.trace F E z) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  apply TensorProduct.AlgebraTensorModule.ext
  intro a e
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, LinearMap.baseChange_tmul]

theorem symp_map (σ : E →ₐ[F] E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    symp (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1) (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (y.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) = algebraMap F R (symp σ (-1) JA JB x y) := by
  have hc : ∀ z : E, Algebra.TensorProduct.map (AlgHom.id R R) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (σ z) := by
    intro z
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hT : hTens (Algebra.TensorProduct.map (AlgHom.id R R) σ) (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
      (y.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R (hTens σ JA JB x y) := by
    simp only [hTens, Matrix.map_apply, hc, map_sum, map_mul]
  simp only [symp]
  rw [hT, ← trace_inclR_divisor R]
  congr 1
  simp

theorem exists_darboux [CharZero F] [Invertible (2 : R)] (h2 : finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : ∀ i j, σ (JA j i) = JA i j) (hB : ∀ i j, σ (JB j i) = -JB i j) (hA' : JA.det ≠ 0) (hB' : JB.det ≠ 0) :
    ∃ co : Darboux (symp (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1)
      (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))) (α × β),
      ∀ x : Matrix α β E, ∃ y z : α × β → F, co.e (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) =
        (fun k => algebraMap F R (y k), fun k => algebraMap F R (z k)) := by
  classical
  have halt := isAlt_sympBil σ hσ hA hB
  have hbij := bijective_sympBil σ hσ hA' hB'
  have hrank : Module.finrank F (Matrix α β E) = 2 * Fintype.card (α × β) := by
    rw [Module.finrank_matrix, h2, Fintype.card_prod]
    ring
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank halt hbij hrank
  let e := (Fintype.equivFin (α × β)).symm
  let b := b₀.reindex (e.sumCongr e)
  have hb : GlobalTheory.IsSymplecticBasis (sympBil σ (-1) JA JB) b := hb₀.reindex e
  let bR : Basis ((α × β) ⊕ (α × β)) R (Matrix α β (R ⊗[F] E)) := (b.baseChange R).map (matBC R)
  have hbR : ∀ i, bR i = (b i).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) := by
    intro i
    rw [Basis.map_apply, Basis.baseChange_apply, matBC_one]
  have hrep : ∀ (x : Matrix α β E) i,
      bR.repr (x.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) i = algebraMap F R (b.repr x i) := by
    intro x i
    rw [← matBC_one, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  let BR := sympBil (R := R) (Algebra.TensorProduct.map (AlgHom.id R R) σ) (-1)
    (JA.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) (JB.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R))
  have hbv : ∀ i j, BR (bR i) (bR j) = algebraMap F R (sympBil σ (-1) JA JB (b i) (b j)) := by
    intro i j
    rw [hbR, hbR]
    exact symp_map R σ JA JB (b i) (b j)
  obtain ⟨co, hco⟩ := exists_darboux_of_basis BR bR
    (fun i j => by rw [hbv, hb.left_left, map_zero])
    (fun i j => by rw [hbv, hb.right_right, map_zero])
    (fun i => by rw [hbv, hb.left_right, if_pos rfl, map_one])
    (fun i j hij => by rw [hbv, hb.left_right, if_neg hij, map_zero])
    (fun i => by rw [hbv, hb.right_left halt, if_pos rfl, map_neg, map_one])
    (fun i j hij => by rw [hbv, hb.right_left halt, if_neg hij, map_zero])
  refine ⟨co, fun x => ⟨fun k => b.repr x (.inl k), fun k => b.repr x (.inr k), ?_⟩⟩
  rw [hco]
  ext k <;> simp [hrep]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpos := h.2.2 (star v) (by rwa [Ne, star_eq_zero])
  rw [star_star, hv, dotProduct_zero, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end General

end GlobalTheory.RatDarboux

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem GlobalTheory.RatDarboux.exists_rational_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY
  obtain ⟨_, _, h2, hconj⟩ := hB.cm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    apply τ.injective
    rw [hconj τ, hconj τ, star_star]
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
  have hA' : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    rw [← show (B.emb w).1 X.J.det = (X.J.map (B.emb w).1).det from RingHom.map_det _ _, h0, map_zero]
  have hB' : Y.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hY.cartan w)
    rw [Matrix.det_smul, ← show (B.emb w).1 Y.J.det = (Y.J.map (B.emb w).1).det from RingHom.map_det _ _, h0,
      map_zero, mul_zero]
  exact GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hX.herm hY.skew hA' hB'
