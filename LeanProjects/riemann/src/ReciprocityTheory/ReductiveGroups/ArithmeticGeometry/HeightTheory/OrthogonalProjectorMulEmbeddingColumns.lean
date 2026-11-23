import ReciprocityTheory.SemistableReduction.LatSemiSt

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

section Proj

variable {K : Type} [Field K] {r k : ℕ}

noncomputable def hBm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l j => σ (b j l)

noncomputable def hPm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin r) ℂ :=
  1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ

noncomputable def hns {r : ℕ} (x : Fin r → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

private theorem linearIndependent_map_ringHom_complex' (σ : K →+* ℂ) {s : Type*} [Fintype s] {v : s → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  let A : Matrix (Fin r) s K := Matrix.of fun l i => v i l
  have hAv : ∀ t : s → K, A *ᵥ t = ∑ i, t i • v i := by
    intro t
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    have h1 : ∑ i, t i • v i = 0 := by rw [← hAv]; exact ht
    funext i
    exact Fintype.linearIndependent_iff.mp hv t h1 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hker
  have hLA : LinearMap.toMatrix' g * A = 1 := by
    have e : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have := congrArg LinearMap.toMatrix' hg
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
    rwa [e] at this
  have hLAσ : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hLA]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hAc : A.map σ *ᵥ c = 0 := by
    rw [← hc]
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hc0 : c = 0 := by
    calc c = ((LinearMap.toMatrix' g).map σ * A.map σ) *ᵥ c := by rw [hLAσ, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

theorem linearIndependent_map_embedding (σ : K →+* ℂ) {ι : Type*} {v : ι → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_map_ringHom_complex' σ (hv.comp (Subtype.val : s → ι) Subtype.val_injective)

theorem embeddingColumns_mulVec (σ : K →+* ℂ) (b : Fin k → Fin r → K) (z : Fin k → ℂ) :
    hBm σ b *ᵥ z = ∑ j, z j • fun l => σ (b j l) := by
  funext l
  simp [hBm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem isUnit_det_embeddingGram (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    IsUnit ((hBm σ b)ᴴ * hBm σ b).det := by
  have hli := linearIndependent_map_embedding σ hb
  have hinj : Function.Injective (hBm σ b).mulVec := by
    intro x y hxy
    have h1 : ∑ j, (x - y) j • (fun l => σ (b j l)) = 0 := by
      rw [← embeddingColumns_mulVec, Matrix.mulVec_sub, hxy, sub_self]
    have h2 := Fintype.linearIndependent_iff.mp hli (x - y) h1
    funext j
    exact sub_eq_zero.mp (h2 j)
  have hker : LinearMap.ker ((hBm σ b)ᴴ * hBm σ b).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self, LinearMap.ker_eq_bot]
    exact hinj
  have hinj2 : Function.Injective ((hBm σ b)ᴴ * hBm σ b).mulVec := LinearMap.ker_eq_bot.mp hker
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj2)

theorem conjTranspose_mul_orthogonalProjector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    (hBm σ b)ᴴ * hPm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, sub_self]

theorem orthogonalProjector_mul_embeddingColumns (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hBm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one, sub_self]

theorem orthogonalProjector_conjTranspose (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by
  simp only [hPm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem orthogonalProjector_mul_self (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hPm σ b = hPm σ b := by
  have h := conjTranspose_mul_orthogonalProjector σ hb
  calc hPm σ b * hPm σ b
      = (1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) * hPm σ b := rfl
    _ = hPm σ b - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * ((hBm σ b)ᴴ * hPm σ b) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = hPm σ b := by rw [h, Matrix.mul_zero, sub_zero]

theorem orthogonalProjector_orthogonal (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_embeddingColumns σ hb, Matrix.vecMul_zero, zero_dotProduct]

theorem normSqSum_add_of_orthogonal {r : ℕ} (a c : Fin r → ℂ) (h : star a ⬝ᵥ c = 0) :
    hns (a + c) = hns a + hns c := by
  unfold hns
  have h' : ∑ i, (a i * (starRingEnd ℂ) (c i)).re = 0 := by
    have h1 : ∑ i, a i * (starRingEnd ℂ) (c i) = (starRingEnd ℂ) (star a ⬝ᵥ c) := by
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [← Complex.re_sum, h1, h, map_zero, Complex.zero_re]
  simp only [Pi.add_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, h', mul_zero, add_zero]

theorem orthogonalProjector_mulVec_ne_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∉ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) ≠ 0 := by
  intro h0
  have hli := linearIndependent_map_embedding σ ((linearIndependent_fin_cons).mpr ⟨hb, hq⟩)
  have hcons : (fun i l => σ ((Fin.cons q b : Fin (k + 1) → Fin r → K) i l)) =
      (Fin.cons (fun l => σ (q l)) (fun j l => σ (b j l)) : Fin (k + 1) → Fin r → ℂ) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hcons, linearIndependent_fin_cons] at hli
  apply hli.2
  have hv : (fun i => σ (q i)) =
      (hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) *ᵥ fun i => σ (q i) := by
    unfold hPm at h0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have hv2 : (fun i => σ (q i)) =
      hBm σ b *ᵥ (((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ fun i => σ (q i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hv
  rw [hv2, embeddingColumns_mulVec]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem orthogonalProjector_mulVec_eq_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∈ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have h1 : (fun i => σ ((∑ j, c j • b j) i)) = hBm σ b *ᵥ fun j => σ (c j) := by
    rw [embeddingColumns_mulVec]
    funext i
    simp [Finset.sum_apply, map_sum, map_mul]
  rw [h1, Matrix.mulVec_mulVec, orthogonalProjector_mul_embeddingColumns σ hb, Matrix.zero_mulVec]

end Proj

section PT

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem crossGram_eq_embeddingColumns (σ : K →+* ℂ) {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramX 1 σ b c = (hBm σ b)ᴴ * hBm σ c := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramX, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem gramMatrix_eq_embeddingColumns (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC 1 σ b = (hBm σ b)ᴴ * hBm σ b := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem quotientGram_eq_projector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) (i j : Fin m) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c i j =
      star (hPm σ b *ᵥ fun l => σ (c i l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (c j l)) := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin r) (Fin m) ℂ) (i j : Fin m),
      (Cᴴ * M * C) i j = star (fun l => C l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
    intro M C i j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hq : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
    rw [gramMatrix_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, crossGram_eq_embeddingColumns]
    unfold hPm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hq, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_self σ hb]
  rfl

end PT

end ReciprocityTheory.ChartRestriction.G.T0
