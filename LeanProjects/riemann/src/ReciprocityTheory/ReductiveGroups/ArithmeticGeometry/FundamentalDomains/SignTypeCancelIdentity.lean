import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PosDefOfBound

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma bound_castLE {n : ℕ} (h : n ≤ X.p0) (Z : X.Coord) (τ : X.Ψ) (y : Fin n → ℂ) :
    nsq ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) ≤
      X.zN Z ^ 2 * nsq y := by
  classical
  set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b := by
    intro b
    simp [hz, b.isLt]
  have hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0 := by
    intro c hc
    simp only [hz]
    rw [dif_neg]
    intro hcn
    exact hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩
  have hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) =
      (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z := by
    funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    refine Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_
    · intro c hc
      simp [hz0 c hc]
    · intro b
      simp [hzc b]
  have hnz : nsq z = nsq y := by
    unfold nsq
    exact (Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc])
      (fun b => by simp [hzc b])).symm
  have hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w := by
    intro q w
    unfold nsq
    simp
  have hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) =
      nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c)) := by
    intro w
    rw [← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]
    congr 1
    funext m
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hop0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := by
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
    unfold Data.zN
    exact le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ
  rw [hvec, hmap, ← hnz, ← hconj z]
  calc nsq (Matrix.of (Z τ) *ᵥ fun c => conj (z c))
      ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq (fun c => conj (z c)) := nsq_mulVec_le_opN _ _
    _ ≤ X.zN Z ^ 2 * nsq (fun c => conj (z c)) := by
      gcongr
      exact nsq_nonneg _

lemma det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dif_neg (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dif_neg]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega

lemma psgn_add (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]

lemma signType_cancel_identity (k : ℕ) (D : ℂ) (hD : 0 < D.re) : 0 < (-1 : ℝ) ^ k * (((-1 : ℂ) ^ k) * D).re := by
  have h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]
  norm_num
  exact hD

lemma pos_re_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) : 0 < M.det.re := by
  exact (Complex.pos_iff.mp hM.det_pos).1

lemma minor_le {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd

lemma minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)

theorem xZ_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) :
    X.xZ x Z ∈ X.dom := by
  rw [Data.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * X.lowBlock Z τ).det ≠ 0
    rw [Matrix.det_mul, det_lowBlock, mul_one]
    exact (hx τ).1
  · by_cases hip : (i : ℕ) ≤ X.p0
    · exact minor_le X ho hZ τ i hip
    · have hi := i.isLt
      have := X.p0_le
      exact minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
