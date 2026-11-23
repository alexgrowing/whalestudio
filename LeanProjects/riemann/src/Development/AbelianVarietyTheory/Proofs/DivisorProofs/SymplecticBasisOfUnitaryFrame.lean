import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

open Module

theorem exists_isSymplecticBasis_extend_family {R M ι : Type} [Field R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (hp : Function.Injective B)
    {v f : ι → M} (hf : IsSymplecticFamily B v f fun _ => 1) :
    ∃ (g : ℕ) (b : Basis ((ι ⊕ Fin g) ⊕ (ι ⊕ Fin g)) R M), IsSymplecticBasis B b ∧
      (∀ i, b (.inl (.inl i)) = v i) ∧ ∀ i, b (.inr (.inl i)) = f i := by
  classical
  let N : Submodule R M := (⨅ i, LinearMap.ker (B (v i))) ⊓ ⨅ i, LinearMap.ker (B (f i))
  have hmem : ∀ y, y ∈ N ↔ (∀ i, B (v i) y = 0) ∧ ∀ i, B (f i) y = 0 := fun y => by
    simp [N, Submodule.mem_iInf]
  have hdec : ∀ y, ∃ a b : ι → R, ∃ y' ∈ N, y = ∑ i, a i • v i + ∑ i, b i • f i + y' := by
    intro y
    refine ⟨fun i => B y (f i), fun i => B (v i) y,
      y - ∑ i, B y (f i) • v i - ∑ i, B (v i) y • f i, (hmem _).2 ⟨fun k => ?_, fun k => ?_⟩,
      by abel⟩
    · simp [hf.left_left, hf.left_right]
    · simp [hf.right_right, hf.right_left hB, ← hB.neg_eq y]
  obtain ⟨g, e', f', d, h', hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB N (by
    intro x hx hx0
    refine (injective_iff_map_eq_zero B).1 hp x (LinearMap.ext fun y => ?_)
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    simp [hx0 y' hy', fun i => hB.eq_iff.1 (((hmem x).1 hx).1 i),
      fun i => hB.eq_iff.1 (((hmem x).1 hx).2 i)])
  have he' : ∀ i, e' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have h'' : IsSymplecticFamily B e' (fun i => (d i)⁻¹ • f' i) fun _ => 1 :=
    ⟨h'.left_left, fun i j => by simp [h'.right_right], fun i => by simp [h'.left_right_self, hd i],
      fun i j hij => by simp [h'.left_right_ne i j hij]⟩
  have hs := IsSymplecticFamily.sum hB hf h'' (fun i j => ((hmem _).1 (he' j)).1 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).1 i) (fun i j => ((hmem _).1 (he' j)).2 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).2 i)
  have h1 : (Sum.elim (fun _ : ι => (1 : R)) fun _ : Fin g => (1 : R)) = fun _ => 1 := by
    funext i; cases i <;> rfl
  rw [h1] at hs
  have hsp : ⊤ ≤ Submodule.span R (Set.range (Sum.elim (Sum.elim v e')
      (Sum.elim f fun i => (d i)⁻¹ • f' i))) := by
    intro y _
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)) ?_
    · exact Submodule.subset_span ⟨Sum.inl (Sum.inl i), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩
    · rw [← hspan] at hy'
      refine Submodule.span_le.2 ?_ hy'
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl (Sum.inr i), rfl⟩
      · have : Sum.elim e' f' (Sum.inr i) = d i • (d i)⁻¹ • f' i := by simp [smul_smul, hd i]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩)
  refine ⟨g, Basis.mk (hs.linearIndependent fun _ => one_ne_zero) hsp, ?_, fun i => by simp, fun i => by simp⟩
  simpa [IsSymplecticBasis, IsSymplecticBasisOfType] using hs

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]

noncomputable def colTraceBil (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm F (Fin d → E) :=
  LinearMap.mk₂ F (fun f g => Algebra.trace F E (-1 * form σ K f g))
    (fun x x' y => by simp only [form, add_dotProduct, mul_add, map_add])
    (fun a x y => by simp only [form, smul_dotProduct, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.add_apply, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem colTraceBil_apply (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (f g : Fin d → E) :
    colTraceBil σ K f g = Algebra.trace F E (-1 * form σ K f g) := rfl

theorem nondegenerate_colTraceBil [CharZero F] [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a)
    {d : ℕ} {K : Matrix (Fin d) (Fin d) E} (hK : K.det ≠ 0) : (colTraceBil σ K).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine Matrix.eq_zero_of_vecMul_eq_zero hK (funext fun l => ?_)
  refine (traceForm_nondegenerate F E).1 _ fun a => ?_
  have := LinearMap.congr_fun hf (Pi.single l (σ (-a)))
  rw [colTraceBil_apply, LinearMap.zero_apply] at this
  rw [Algebra.traceForm_apply, ← this]
  congr 1
  have h : (fun i => σ ((Pi.single l (σ (-a)) : Fin d → E) i)) = Pi.single l (-a) := by
    funext i
    by_cases hi : i = l
    · subst hi; simp only [Pi.single_eq_same, hσ]
    · simp [hi]
  rw [form, h, Matrix.dotProduct_mulVec, dotProduct_single]
  ring

theorem symp_vecMulVec_right (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E) (w : Fin d → E) :
    symp σ (-1) J K m (Matrix.vecMulVec v w) = colTraceBil σ K (fun l => form σ J (fun r => m r l) v) w := by
  rw [colTraceBil_apply, symp]
  congr 2
  simp only [hTens, form, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_vecMulVec (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (u v : Fin n → E) (f w : Fin d → E) :
    symp σ (-1) J K (Matrix.vecMulVec u f) (Matrix.vecMulVec v w) = colTraceBil σ K (form σ J u v • f) w := by
  rw [symp_vecMulVec_right]
  congr 2
  funext l
  simp only [form, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) : form σ J u v = σ (form σ J v u) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem exists_frame_symplectic_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E),
    (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 → IsFrameU σ J x y →
    ∃ (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
      (blk : Fin q → Finset (Fin n × Fin d)),
      (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) ∧
      (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) := by
  intro F E _ _ _ _ _ σ n d q J K x y hσ h2 hJ hJ' hK hK' hfr
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have halt := GlobalTheory.RatDarboux.isAlt_sympBil σ hσ hJ hK
  have hinj := (GlobalTheory.RatDarboux.bijective_sympBil σ hσ hJ' hK').1
  have hnd := nondegenerate_colTraceBil σ hσ hK'
  set B := GlobalTheory.RatDarboux.sympBil σ (-1) J K with hBdef
  have hB : ∀ a b, B a b = symp σ (-1) J K a b := fun _ _ => rfl
  let g := Module.finBasis F (Fin d → E)
  let f := (colTraceBil σ K).dualBasis hnd g
  have hfg : ∀ k l, colTraceBil σ K (f k) (g l) = if l = k then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left hnd g
  have hyx : ∀ i j, form σ J (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [form_swap σ hσ hJ, hfr.2.2]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hfam : IsSymplecticFamily B
      (fun p : Fin q × Fin (Module.finrank F (Fin d → E)) => Matrix.vecMulVec (y p.1) (f p.2))
      (fun p => Matrix.vecMulVec (x p.1) (g p.2)) fun _ => 1 := by
    refine ⟨fun p r => ?_, fun p r => ?_, fun p => ?_, fun p r hpr => ?_⟩
    · simp [hB, symp_vecMulVec, hfr.2.1]
    · simp [hB, symp_vecMulVec, hfr.1]
    · simp [hB, symp_vecMulVec, hyx, hfg]
    · rw [hB, symp_vecMulVec, hyx]
      by_cases h : p.1 = r.1
      · have h' : ¬ r.2 = p.2 := fun h' => hpr (Prod.ext h h'.symm)
        simp [h, hfg, h']
      · simp [h]
  obtain ⟨s, b₀, hb₀, hl, hr⟩ := exists_isSymplecticBasis_extend_family halt hinj hfam
  have hcard : Fintype.card ((Fin q × Fin (Module.finrank F (Fin d → E))) ⊕ Fin s) =
      Fintype.card (Fin n × Fin d) := by
    have h1 := IsSymplecticBasisOfType.finrank_eq b₀
    rw [Module.finrank_matrix, h2] at h1
    rw [Fintype.card_prod (Fin n)]
    omega
  let ε := Fintype.equivOfCardEq hcard
  have hb := hb₀.reindex ε
  have hbl : ∀ k, b₀.reindex (ε.sumCongr ε) (.inl (ε k)) = b₀ (.inl k) := fun k => by simp
  have hbr : ∀ k, b₀.reindex (ε.sumCongr ε) (.inr (ε k)) = b₀ (.inr k) := fun k => by simp
  have hcol : ∀ (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E)
      (c : Basis (Fin (Module.finrank F (Fin d → E))) F (Fin d → E)),
      (∀ k, B m (Matrix.vecMulVec v (c k)) = 0) → ∀ l, form σ J (fun r => m r l) v = 0 := by
    intro m v c h l
    have h0 : colTraceBil σ K (fun l => form σ J (fun r => m r l) v) = 0 :=
      c.ext fun k => by rw [← symp_vecMulVec_right, ← hB, h, LinearMap.zero_apply]
    exact congrFun (hnd.1 _ fun w => by rw [h0, LinearMap.zero_apply]) l
  refine ⟨b₀.reindex (ε.sumCongr ε), fun i => Finset.univ.image fun k => ε (.inl (i, k)), ?_,
    hb.left_left, hb.right_right, hb.left_right, hb.right_left halt, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k', -, h⟩ := Finset.mem_image.1 ha'
    exact hij (congrArg Prod.fst (Sum.inl_injective (ε.injective h))).symm
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨f k, by rw [hbl, hl]⟩
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨g k, by rw [hbr, hr]⟩
  · intro k hk l i
    obtain ⟨k, rfl⟩ := ε.surjective k
    rcases k with ⟨j, k⟩ | k
    · exact absurd (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩) (hk j)
    rw [hbl, hbr]
    refine ⟨hcol _ _ g (fun k' => ?_) l, hcol _ _ f (fun k' => ?_) l, hcol _ _ g (fun k' => ?_) l,
      hcol _ _ f (fun k' => ?_) l⟩
    · rw [← hr (i, k'), hb₀.left_right]; simp
    · rw [← hl (i, k'), hb₀.left_left]
    · rw [← hr (i, k'), hb₀.right_right]
    · rw [← hl (i, k'), hb₀.right_left halt]; simp

end GlobalTheory.ThKTorus
