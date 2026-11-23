import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality

namespace ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

lemma opN_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ v, OrthonormalChartBounds.nsq (A *ᵥ v) ≤ δ ^ 2 * OrthonormalChartBounds.nsq v) : Data.opN A ≤ δ := by
  unfold Data.opN
  apply Real.sSup_le _ hδ
  rintro t ⟨v, hv, rfl⟩
  have hpos : 0 < ∑ j, ‖v j‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc Real.sqrt (∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ Real.sqrt (δ ^ 2 * ∑ j, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt (h v)
    _ = δ * Real.sqrt (∑ j, ‖v j‖ ^ 2) := by rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_Z (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (y : Fin r → Fin r → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, X.p0 ≤ (j : ℕ) → w j = 0) →
      ReciprocityTheory.MultiplicativeHeights.negSq X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j) ≤
        δ ^ 2 * ReciprocityTheory.MultiplicativeHeights.posSq X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j) ∧
      (w ≠ 0 → 0 < (ReciprocityTheory.MultiplicativeHeights.jForm X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j)
        ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j)).re)) :
    ∃ Zτ : Fin (r - X.p0) → Fin X.p0 → ℂ, Data.opN (Matrix.of Zτ) ≤ δ ∧
      ∀ Z : X.Coord, Z τ = Zτ →
        Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le a)) =
          Submodule.span ℂ (Set.range fun a : Fin X.p0 => y (Fin.castLE X.p0_le a)) := by
  classical
  set Q := (mat x τ)⁻¹ with hQ
  have hinv : ∀ u : Fin r → ℂ, mat x τ *ᵥ (Q *ᵥ u) = u := fun u => by
    rw [hQ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hx τ).1), Matrix.one_mulVec]
  set c : Fin X.p0 → Fin r → ℂ := fun a => Q *ᵥ y (Fin.castLE X.p0_le a) with hc
  set A : Matrix (Fin X.p0) (Fin X.p0) ℂ := Matrix.of fun i a => c a (Fin.castLE X.p0_le i) with hA
  set B : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ := Matrix.of fun m a => c a (OrthonormalChartBounds.nI X m) with hB
  have hcomb : ∀ w' : Fin X.p0 → ℂ, ∃ w : Fin r → ℂ, (∀ j : Fin r, X.p0 ≤ (j : ℕ) → w j = 0) ∧
      (w' ≠ 0 → w ≠ 0) ∧ Q *ᵥ ∑ j, w j • y j = ∑ a, w' a • c a := by
    intro w'
    refine ⟨fun j => if h : (j : ℕ) < X.p0 then w' ⟨j, h⟩ else 0, fun j hj => dif_neg (by omega), ?_, ?_⟩
    · intro hw' hw
      apply hw'
      funext a
      have := congrFun hw (Fin.castLE X.p0_le a)
      simpa [Fin.val_castLE, a.isLt] using this
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
      rw [PositiveSpanMatrices.sum_split X.p0_le]
      simp [PositiveSpanMatrices.kap, Fin.val_castLE, hc]
  have hpa : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.mjpa X (∑ a, w' a • c a) = A *ᵥ w' := fun w' => by
    funext i
    simp [OrthonormalChartBounds.mjpa, hA, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hpb : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.mjpb X (∑ a, w' a • c a) = B *ᵥ w' := fun w' => by
    funext m
    simp [OrthonormalChartBounds.mjpb, hB, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hpos : ∀ u : Fin r → ℂ, ReciprocityTheory.MultiplicativeHeights.posSq X.p0 u = OrthonormalChartBounds.nsq (OrthonormalChartBounds.mjpa X u) := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.posSq OrthonormalChartBounds.nsq OrthonormalChartBounds.mjpa
    rw [PositiveSpanMatrices.sum_split X.p0_le]
    simp [PositiveSpanMatrices.kap, Fin.val_castLE]
  have hneg : ∀ u : Fin r → ℂ, ReciprocityTheory.MultiplicativeHeights.negSq X.p0 u = OrthonormalChartBounds.nsq (OrthonormalChartBounds.mjpb X u) := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.negSq OrthonormalChartBounds.nsq OrthonormalChartBounds.mjpb
    rw [PositiveSpanMatrices.sum_split X.p0_le]
    simp [PositiveSpanMatrices.kap, OrthonormalChartBounds.nI, Fin.val_castLE]
  have hjre : ∀ u : Fin r → ℂ, (ReciprocityTheory.MultiplicativeHeights.jForm X.p0 u u).re =
      ReciprocityTheory.MultiplicativeHeights.posSq X.p0 u - ReciprocityTheory.MultiplicativeHeights.negSq X.p0 u := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.posSq ReciprocityTheory.MultiplicativeHeights.negSq ReciprocityTheory.MultiplicativeHeights.sgn
    rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
    split_ifs <;> simp [← Complex.ofReal_pow]
  have hkey : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.nsq (B *ᵥ w') ≤ δ ^ 2 * OrthonormalChartBounds.nsq (A *ᵥ w') ∧
      (w' ≠ 0 → OrthonormalChartBounds.nsq (B *ᵥ w') < OrthonormalChartBounds.nsq (A *ᵥ w')) := fun w' => by
    obtain ⟨w, hw0, hne, hw⟩ := hcomb w'
    obtain ⟨h1, h2⟩ := hg w hw0
    rw [hw, hneg, hpos, hpb, hpa] at h1
    refine ⟨h1, fun h => ?_⟩
    have := h2 (hne h)
    rw [hw, hjre, hneg, hpos, hpb, hpa] at this
    linarith
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := (hkey v).2 hv
    rw [hAv, OrthonormalChartBounds.nsq_zero'] at this
    linarith [OrthonormalChartBounds.nsq_nonneg (B *ᵥ v)]
  have hext : ∀ u u' : Fin r → ℂ, OrthonormalChartBounds.mjpa X u = OrthonormalChartBounds.mjpa X u' → OrthonormalChartBounds.mjpb X u = OrthonormalChartBounds.mjpb X u' →
      u = u' := by
    intro u u' ha hb
    funext k
    rcases PositiveSpanMatrices.fin_cases_split X.p0_le k with ⟨b, rfl⟩ | ⟨m, rfl⟩
    · exact congrFun ha b
    · exact congrFun hb m
  refine ⟨B * A⁻¹, ?_, fun Z hZ => ?_⟩
  · apply opN_le _ hδ
    intro v
    have hAv : A *ᵥ (A⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hAdet), Matrix.one_mulVec]
    have := (hkey (A⁻¹ *ᵥ v)).1
    rw [hAv, Matrix.mulVec_mulVec] at this
    exact this
  · have hsgl : ∀ b : Fin X.p0, (fun a => A a b) = A *ᵥ Pi.single b 1 := fun b => by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have e2 : ∀ b : Fin X.p0, OrthonormalChartBounds.mjg X Z τ (fun a => A a b) = c b := fun b => by
      apply hext
      · rw [OrthonormalChartBounds.mjg_pa]
        rfl
      · rw [OrthonormalChartBounds.mjg_pb, hZ, hsgl b]
        change (B * A⁻¹) *ᵥ (A *ᵥ Pi.single b 1) = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hAdet),
          Matrix.mul_one]
        funext m
        simp [OrthonormalChartBounds.mjpb, hB, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcol : ∀ b : Fin X.p0, y (Fin.castLE X.p0_le b) =
        ∑ a, A a b • col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le a) := fun b =>
      calc y (Fin.castLE X.p0_le b) = mat x τ *ᵥ c b := (hinv _).symm
        _ = mat x τ *ᵥ OrthonormalChartBounds.mjg X Z τ (fun a => A a b) := by rw [e2]
        _ = ∑ a, (fun a => A a b) a • X.colP (X.xZ x Z) τ a := (OrthonormalChartBounds.mj_sum_colP X x Z τ _).symm
        _ = _ := rfl
    exact (PositiveSpanMatrices.span_eq_of_mat _ _ A hAdet hcol).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence
