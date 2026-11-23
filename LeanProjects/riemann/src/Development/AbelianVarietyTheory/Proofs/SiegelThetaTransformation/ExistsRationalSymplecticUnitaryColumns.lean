import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticActionOfPeriodLatticeMap

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Classical Kronecker

namespace GlobalTheory.ColumnSymplectic

variable {n g : ℕ}

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) :
    blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  simp only [blk, of_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

theorem blk_mul (A B : Matrix (Fin g) (Fin g) ℂ) : blk n A * blk n B = blk n (A * B) := by
  rw [blk_eq, blk_eq, blk_eq, ← mul_kronecker_mul, one_mul]

theorem blk_one : blk n (1 : Matrix (Fin g) (Fin g) ℂ) = 1 := by
  rw [blk_eq, one_kronecker_one]

theorem blk_mulVec (A : Matrix (Fin g) (Fin g) ℂ) (w : Fin n × Fin g → ℂ) :
    blk n A *ᵥ w = fun p => (A *ᵥ fun i => w (p.1, i)) p.2 := by
  funext p
  simp only [mulVec, dotProduct, blk, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem blk_mem_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · show (blk n τ)ᵀ = blk n τ
    ext p q
    simp only [transpose_apply, blk, of_apply]
    by_cases e : p.1 = q.1
    · rw [if_pos e.symm, if_pos e]
      exact congrFun (congrFun h.1 p.2) q.2
    · rw [if_neg (Ne.symm e), if_neg e]
  · have e : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ τ.map Complex.im := by
      ext p q
      simp only [map_apply, blk, of_apply, kroneckerMap_apply, one_apply]
      split_ifs <;> simp
    rw [e]
    exact PosDef.one.kronecker h.2

private theorem sum_herm_eq_trace_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G (y k) (y' k) = (y * G * ccT y').trace := by
  simp only [herm, trace, diag, mul_apply, ccT, transpose_apply, map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem sum_herm_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (G : Matrix (Fin r) (Fin r) E)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G ((h * y) k) ((h * y') k) = ∑ k, herm G (y k) (y' k) := by
  rw [sum_herm_eq_trace_mul_ccT, sum_herm_eq_trace_mul_ccT, Base.ccT_mul]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, hu, Matrix.mul_one]

theorem sum_EF_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X ((h * y) k) ((h * y') k) = ∑ k, EF X (y k) (y' k) := by
  simp only [EF_def, ← map_sum, ← Finset.mul_sum]
  rw [sum_herm_mul hu]

private theorem crd_dotProduct_sub_eq_neg_sum_EF (hs : IsSympl X bas) (Z Z' : Matrix (Fin n) (Fin r) E) :
    (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inl p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inr p.2)) -
      (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inr p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inl p.2)) =
      -∑ k, EF X (Z k) (Z' k) := by
  simp only [EF_crd hs, dotProduct, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_neg,
    ← Finset.sum_sub_distrib]

variable (bas) in

noncomputable def famOf (u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) : Matrix (Fin n) (Fin r) E :=
  Matrix.of fun k => vecQ X bas (Sum.elim (fun i => u.1 (k, i)) fun i => u.2 (k, i))

noncomputable def colMap (hs : IsSympl X bas) (h : Matrix (Fin n) (Fin n) E) :
    ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) →ₗ[ℚ] ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) where
  toFun u := (fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inl p.2),
    fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inr p.2))
  map_add' u v := by
    have : famOf bas (u + v) = famOf bas u + famOf bas v := by
      refine funext fun k => ?_
      change vecQ X bas _ = vecQ X bas _ + vecQ X bas _
      rw [← vecQ_add]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (u + v)) k = (h * famOf bas u) k + (h * famOf bas v) k := fun k => by
      rw [this, Matrix.mul_add]; rfl
    simp only [e, crd_add hs]
    rfl
  map_smul' q u := by
    have : famOf bas (q • u) = q • famOf bas u := by
      refine funext fun k => ?_
      change vecQ X bas _ = q • vecQ X bas _
      rw [← vecQ_smul]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (q • u)) k = q • (h * famOf bas u) k := fun k => by
      rw [this, Matrix.mul_smul]; rfl
    simp only [e, crd_smul hs]
    rfl

theorem colMap_form (hs : IsSympl X bas) {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (u v : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) :
    (colMap hs h u).1 ⬝ᵥ (colMap hs h v).2 - (colMap hs h u).2 ⬝ᵥ (colMap hs h v).1 =
      u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 := by
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  have e1 := crd_dotProduct_sub_eq_neg_sum_EF hs (h * famOf bas u) (h * famOf bas v)
  have e2 := crd_dotProduct_sub_eq_neg_sum_EF hs (famOf bas u) (famOf bas v)
  rw [sum_EF_mul hu, ← e2] at e1
  simp only [hcrd, Sum.elim_inl, Sum.elim_inr] at e1
  exact e1

noncomputable def actM (h : Matrix (Fin n) (Fin n) E) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  blockDiagonal fun i => (rowType X (idx i)).mapMatrix h

theorem actM_mulVec (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    (actM idx h *ᵥ fun p => z p.1 p.2) = fun p => Dict.hAct X idx h z p.1 p.2 := by
  funext p
  simp only [actM, Dict.hAct, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, RingHom.mapMatrix_apply, map_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_actM (h : Matrix (Fin n) (Fin n) E) :
    (actM idx h).det = ∏ i, rowType X (idx i) h.det := by
  rw [actM, det_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ => (RingHom.map_det _ _).symm

theorem per_mul (x : Frame X.Ψ r) (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E)
    (k : Fin n) : per X x ((h * y) k) ∘ idx = Dict.hAct X idx h (fun k => per X x (y k) ∘ idx) k := by
  have e : (h * y) k = ∑ k', h k k' • y k' := by
    ext a
    simp [mul_apply, Finset.sum_apply]
  funext i
  rw [e, per_sum]
  simp only [Function.comp_apply, Finset.sum_apply, per_smul, Dict.hAct]

theorem conj_mulVec (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    ((blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) =
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  have hH : (hMat X bas idx x)⁻¹ * hMat X bas idx x = 1 :=
    nonsing_inv_mul _ (isUnit_det_hMat (idx := idx) hs hx)
  have e3 : (blk n (hMat X bas idx x)⁻¹ *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = fun p => z p.1 p.2 := by
    rw [blk_mulVec]
    funext p
    simp only [mulVec_mulVec, hH, one_mulVec]
  rw [← mulVec_mulVec, e3, ← mulVec_mulVec, actM_mulVec, blk_mulVec]

theorem exists_symplectic_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  intro E _ _ _ r X g bas idx n hs _ h hu
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  obtain ⟨s, hsS, hact⟩ := GlobalTheory.SymplecticPeriods.exists_symplectic_action (Fin n × Fin g)
    (colMap hs h) (colMap_form hs hu)
  refine ⟨s, hsS, fun x hx => ?_⟩
  have hT : tauMat X bas idx x ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩
  have hB := blk_mem_siegel (n := n) hT
  have hUnit := isUnit_det_hMat (idx := idx) hs hx
  have key : ∀ u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ),
      (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
          (qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2) =
        qv (colMap hs h u).1 + blk n (tauMat X bas idx x) *ᵥ qv (colMap hs h u).2 := by
    intro u
    have ea : qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2 =
        fun p : Fin n × Fin g =>
          (hMat X bas idx x *ᵥ (fun k => per X x (famOf bas u k) ∘ idx) p.1) p.2 := by
      funext p
      rw [hMat_mulVec_per_crd idx hs hx, Pi.add_apply, blk_mulVec]
      simp only [Pi.add_apply, hcrd, Sum.elim_inl, Sum.elim_inr]
      rfl
    rw [ea, conj_mulVec idx hs hx h (fun k => per X x (famOf bas u k) ∘ idx)]
    funext p
    rw [← per_mul idx x h (famOf bas u) p.1, hMat_mulVec_per_crd idx hs hx, Pi.add_apply,
      Pi.add_apply, blk_mulVec]
    rfl
  obtain ⟨e1, e2⟩ := hact _ hB _ _ hB.1 key
  have hdetM : (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹).det =
      ∏ i, rowType X (idx i) h.det := by
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, blk_mul, mul_nonsing_inv _ hUnit, blk_one,
      det_one, one_mul, det_actM]
  have hdeth : h.det ≠ 0 := by
    have := congrArg Matrix.det hu
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have hP : ∏ i, rowType X (idx i) h.det ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hdeth
  rw [e2, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv'] at hdetM
  have hD : (spDen s (blk n (tauMat X bas idx x))).det ≠ 0 := by
    intro hz
    rw [hz, _root_.inv_zero] at hdetM
    exact hP hdetM.symm
  refine ⟨hT, e1.symm, ?_, fun z => ?_⟩
  · rw [← hdetM, mul_inv_cancel₀ hD]
  · rw [← mulVec_transpose, ← e2]
    exact conj_mulVec idx hs hx h z

end GlobalTheory.ColumnSymplectic
