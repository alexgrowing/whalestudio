import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder

noncomputable section

namespace S6.QuotExtension

theorem schur_inner {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (G : Matrix (m ⊕ k) (m ⊕ k) ℂ) (hA : IsUnit G.toBlocks₁₁.det) (β β' : m → ℂ) (γ γ' : k → ℂ)
    (h : ∀ i, (G *ᵥ Sum.elim β' γ') (Sum.inl i) = 0) :
    star (Sum.elim β γ) ⬝ᵥ (G *ᵥ Sum.elim β' γ') =
      star γ ⬝ᵥ ((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ γ') := by
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  set D := G.toBlocks₂₂
  have hG : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  have hv : G *ᵥ Sum.elim β' γ' = Sum.elim (A *ᵥ β' + B *ᵥ γ') (C *ᵥ β' + D *ᵥ γ') := by
    rw [hG, fromBlocks_mulVec]
    rfl
  have h0 : A *ᵥ β' + B *ᵥ γ' = 0 := funext fun i => by simpa [hv] using h i
  have hβ : β' = -((A⁻¹ * B) *ᵥ γ') := by
    have hinv : A⁻¹ *ᵥ (A *ᵥ β') = β' := by rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]
    rw [← hinv, eq_neg_iff_add_eq_zero, ← mulVec_mulVec, ← mulVec_add, h0, mulVec_zero]
  have hw : C *ᵥ β' + D *ᵥ γ' = (D - C * A⁻¹ * B) *ᵥ γ' := by
    rw [hβ, mulVec_neg, mulVec_mulVec, sub_mulVec, Matrix.mul_assoc]
    abel
  rw [hv, h0, hw]
  simp [dotProduct, Fintype.sum_sum_type]

variable {K : Type} [Field K] [NumberField K]

def embMat (σ : K →+* ℂ) {n : ℕ} {ι : Type*} (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun r s => σ (u s r)

omit [NumberField K] in

theorem gramAt_eq {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) : gramAt h σ u = (embMat σ u)ᴴ * h * embMat σ u := by
  ext s t
  simp only [gramAt, embVec, embMat, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply,
    of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring

omit [NumberField K] in

theorem inner_embMat {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (w w' : ι → ℂ) :
    star (embMat σ u *ᵥ w) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w')) = star w ⬝ᵥ (gramAt h σ u *ᵥ w') := by
  rw [star_mulVec, ← dotProduct_mulVec, gramAt_eq, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

omit [NumberField K] in

theorem gramAt_mulVec_apply {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] (u : ι → Fin n → K) (w : ι → ℂ) (s : ι) :
    (gramAt h σ u *ᵥ w) s = star (embVec σ (u s)) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w)) := by
  rw [gramAt_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, conjTranspose_apply, embMat, embVec, of_apply, Pi.star_apply]

theorem exists_smul_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K}
    (ha : ∀ x, a x ≠ 0) (v : Fin n → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ idealLattice a := by
  classical
  choose e he0 hea using fun x => FractionalIdeal.exists_ne_zero_mem_isInteger (ha x)
  obtain ⟨c, hc0, hc⟩ := exists_common_denominator (M := Submodule.span (𝓞 K) {v})
    (Submodule.fg_span_singleton v)
  refine ⟨c * ∏ x, e x, mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun x _ => he0 x), ?_⟩
  rw [idealLattice, Submodule.mem_pi]
  intro x _
  obtain ⟨w, hw⟩ := hc v (Submodule.mem_span_singleton_self v) x
  rw [← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ x)]
  have hx : ((c * (e x * ∏ y ∈ Finset.univ.erase x, e y)) • v) x =
      (w * ∏ y ∈ Finset.univ.erase x, e y) • algebraMap (𝓞 K) K (e x) := by
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_mul, hw]
    ring
  rw [hx]
  exact Submodule.smul_mem _ _ (hea x)

theorem coord_decomp {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n)
    (σ : K →+* ℂ) (x : Fibre σ (idealLattice a)) :
    ∃ β : Fin m → ℂ, latticeCoord σ (idealLattice a) x =
      embMat σ (Sum.elim b c) *ᵥ Sum.elim β (latticeCoord σ (quotLattice a b c hli hmk)
        ((quotProj a b c hli hmk).lTensor (ComplexAt σ) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul z v =>
    refine ⟨fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) * (ofComplex σ).symm z, ?_⟩
    have hu : Sum.elim (fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) *
        (ofComplex σ).symm z) (latticeCoord σ (quotLattice a b c hli hmk)
          ((quotProj a b c hli hmk).lTensor (ComplexAt σ) (z ⊗ₜ v))) =
        fun s => σ ((sumBasis b c hli hmk).repr v s) * (ofComplex σ).symm z := by
      funext s
      rcases s with i | j
      · rfl
      · rw [Sum.elim_inr, LinearMap.lTensor_tmul, latticeCoord_tmul]
        rfl
    rw [hu]
    funext r
    rw [latticeCoord_tmul]
    have hv := congrFun ((sumBasis b c hli hmk).sum_repr (v : Fin n → K)) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sumBasis_apply] at hv
    simp only [mulVec, dotProduct, embMat, of_apply]
    rw [← hv, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    ring
  | add x y hx hy =>
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', hβ'⟩ := hy
    refine ⟨β + β', ?_⟩
    rw [map_add, map_add, map_add, hβ, hβ', ← mulVec_add, Sum.elim_add_add]

theorem orth_sub {n m : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (ha : ∀ x, a x ≠ 0)
    {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x)
    (b : Fin m → Fin n → K) (σ : K →+* ℂ) (y : Fibre σ (idealLattice a))
    (hy : ∀ w : Fibre σ (subLattice a b), ((latticeBundle a d hd hc).metric.form σ).inner
      ((subLattice a b).subtype.lTensor (ComplexAt σ) w) y = 0) (i : Fin m) :
    star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem_idealLattice ha (b i)
  have hW : (⟨t • b i, htv⟩ : idealLattice a) ∈ subLattice a b :=
    Submodule.smul_of_tower_mem (Submodule.span K (Set.range b)) t
      (Submodule.subset_span ⟨i, rfl⟩)
  have h := hy ((1 : ComplexAt σ) ⊗ₜ ⟨_, hW⟩)
  rw [LinearMap.lTensor_tmul] at h
  have h' : star (latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a))) ⬝ᵥ
      (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := h
  have hl : latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a)) = σ (t : K) • embVec σ (b i) := by
    funext r
    rw [latticeCoord_tmul]
    simp [embVec, Algebra.smul_def]
  have hσt : σ (t : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ht
  rw [hl, star_smul, smul_dotProduct, smul_eq_mul] at h'
  exact (mul_eq_zero.mp h').resolve_left (by simpa using hσt)

end S6.QuotExtension

open S6.QuotExtension in

theorem S6.QuotExtension.proof : S6.QuotExtension.Statement := by
  intro K _ _ n a d hd hc ha m k b c hli hmk
  refine ⟨{ incl := (subLattice a b).subtype
            proj := quotProj a b c hli hmk
            incl_injective := (subLattice a b).injective_subtype
            proj_surjective := LinearMap.submoduleMap_surjective _ _
            exact := ?_
            incl_isometric := fun σ x y => rfl
            proj_coisometric := ?_ }, rfl, rfl⟩
  · show ∀ y : idealLattice a, quotProj a b c hli hmk y = 0 ↔ y ∈ Set.range (subLattice a b).subtype
    intro y
    have hker := KLinesQuotIndex.ker_coordProj (sumBasis b c hli hmk)
    have hr : (fun i => sumBasis b c hli hmk (Sum.inl i)) = b :=
      funext fun i => by rw [sumBasis_apply]; rfl
    rw [hr] at hker
    have h1 : quotProj a b c hli hmk y = 0 ↔
        coordProj (sumBasis b c hli hmk) (y : Fin n → K) = 0 := by
      rw [← Submodule.coe_eq_zero]
      exact Iff.rfl
    rw [h1, ← LinearMap.mem_ker, hker]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  · intro σ x y _ hy
    obtain ⟨β, hx⟩ := coord_decomp a b c hli hmk σ x
    obtain ⟨β', hy'⟩ := coord_decomp a b c hli hmk σ y
    have hG := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : IsUnit (gramAt (diagMetric d σ) σ (Sum.elim b c)).toBlocks₁₁.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hG.submatrix Sum.inl_injective).isUnit
    change star (latticeCoord σ (quotLattice a b c hli hmk) _) ⬝ᵥ
        (schurMetric d b c σ *ᵥ latticeCoord σ (quotLattice a b c hli hmk) _) =
      star (latticeCoord σ (idealLattice a) x) ⬝ᵥ
        (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y)
    rw [hx, hy', inner_embMat]
    refine (schur_inner _ hA _ _ _ _ fun i => ?_).symm
    rw [gramAt_mulVec_apply]
    exact (congrArg (fun v => star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ v)) hy').symm.trans
      (orth_sub ha hd hc b σ y hy i)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
