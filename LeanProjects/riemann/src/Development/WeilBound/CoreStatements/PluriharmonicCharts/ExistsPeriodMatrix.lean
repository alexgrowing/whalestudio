import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.PluriharmonicCharts.PeriodGramConj
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenDet

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

open scoped MatrixOrder in
theorem exists_sqrt {m : Type} [Fintype m] [DecidableEq m] {G : Matrix m m ℂ} (h : G.PosDef) :
    ∃ R : Matrix m m ℂ, G = Rᴴ * R ∧ R.det ≠ 0 := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.posSemidef.nonneg
  refine ⟨R, by rw [hR, star_eq_conjTranspose], ?_⟩
  intro h0
  have hz : G.det = 0 := by
    rw [hR, star_eq_conjTranspose, det_mul, h0, mul_zero]
  have hu := (Matrix.isUnit_iff_isUnit_det G).mp h.isUnit
  rw [hz] at hu
  exact not_isUnit_zero hu

private theorem sub_transpose_eq_fromRows_conj_fromBlocks {p q : ℕ} (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (Bm : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ) :
    Aᴴ * Gw * A - (Bmᴴ * Go * Bm)ᵀ =
      (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ * fromBlocks (-Goᵀ) 0 0 Gw *
        fromRows (Bm.map (starRingEnd ℂ)) A := by
  have hN : (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ = fromCols Bmᵀ Aᴴ := by
    ext i (j | j) <;> simp [conjTranspose_apply]
  have h2 : fromBlocks (-Goᵀ) 0 0 Gw * fromRows (Bm.map (starRingEnd ℂ)) A =
      fromRows (-Goᵀ * Bm.map (starRingEnd ℂ)) (Gw * A) := by
    ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type]
  have h3 : Bmᴴᵀ = Bm.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  conv_rhs => rw [Matrix.mul_assoc, h2, hN, fromCols_mul_fromRows]
  rw [transpose_mul, transpose_mul, h3]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

private theorem fromRows_mul_neg_inv_mul_transpose {p q : ℕ} (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (Bm : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ)
    (Ψ : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (hGo : Goᵀ.det ≠ 0)
    (hN : (fromRows (Bm.map (starRingEnd ℂ)) A).det ≠ 0) (hΨd : Ψ.det ≠ 0)
    (hΨ : Ψ = (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ * fromBlocks (-Goᵀ) 0 0 Gw *
        fromRows (Bm.map (starRingEnd ℂ)) A) :
    fromRows (Bm.map (starRingEnd ℂ)) A * (-Ψ⁻¹ * Bmᵀ) = fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) := by
  set Nm := fromRows (Bm.map (starRingEnd ℂ)) A with hNm
  have hNu : IsUnit Nm.det := isUnit_iff_ne_zero.mpr hN
  have hΨu : IsUnit Ψ.det := isUnit_iff_ne_zero.mpr hΨd
  have hGu : IsUnit Goᵀ.det := isUnit_iff_ne_zero.mpr hGo
  have hNh : Nmᴴ = fromCols Bmᵀ Aᴴ := by
    ext i (j | j) <;> simp [hNm, conjTranspose_apply]
  have hDF : fromBlocks (-Goᵀ) 0 0 Gw * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) =
      fromRows (-1) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have : Goᵀ * Goᵀ⁻¹ = 1 := mul_nonsing_inv _ hGu
    ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type, ← this]
  have hW : Ψ * (Nm⁻¹ * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ)) = -Bmᵀ := by
    rw [hΨ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Nm Nm⁻¹,
      mul_nonsing_inv _ hNu, Matrix.one_mul, hDF, hNh, fromCols_mul_fromRows]
    simp
  have hW2 : Nm⁻¹ * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) = -Ψ⁻¹ * Bmᵀ := by
    have := congrArg (fun M => Ψ⁻¹ * M) hW
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hΨu, Matrix.one_mul] at this
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  rw [← hW2, ← Matrix.mul_assoc, mul_nonsing_inv _ hNu, Matrix.one_mul]

private theorem fromBlocks_conj_inv_eq_conj {p q : ℕ} (G : Matrix (Fin q) (Fin q) ℂ) (hG : G.PosDef)
    (Y : Matrix (Fin q) (Fin p) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ) :
    (fromBlocks G⁻¹ Y 0 1)ᴴ * fromBlocks (-G) 0 0 Gw * fromBlocks G⁻¹ Y 0 1 =
      (fromBlocks 1 (G * Y) 0 1)ᴴ * fromBlocks (-G⁻¹) 0 0 Gw * fromBlocks 1 (G * Y) 0 1 := by
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hK : (G⁻¹)ᴴ = G⁻¹ := by
    rw [conjTranspose_nonsing_inv, hG.1.eq]
  have hsplit : fromBlocks G⁻¹ Y 0 (1 : Matrix (Fin p) (Fin p) ℂ) =
      fromBlocks G⁻¹ 0 0 1 * fromBlocks 1 (G * Y) 0 1 := by
    rw [fromBlocks_multiply]
    simp [← Matrix.mul_assoc, nonsing_inv_mul _ hGu]
  have hmid : (fromBlocks G⁻¹ 0 0 (1 : Matrix (Fin p) (Fin p) ℂ))ᴴ * fromBlocks (-G) 0 0 Gw *
      fromBlocks G⁻¹ 0 0 1 = fromBlocks (-G⁻¹) 0 0 Gw := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hK, Matrix.mul_assoc, mul_nonsing_inv _ hGu]
  rw [hsplit, conjTranspose_mul, ← hmid]
  simp only [Matrix.mul_assoc]

private theorem gramOf_sigForm_submatrix_blockEquiv {p q : ℕ} (P : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) :
    (gramOf (sigForm (p + q) p) (P.submatrix (blockEquiv p q).symm (blockEquiv p q).symm)).submatrix
      (blockEquiv p q) (blockEquiv p q) =
      Pᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * P := by
  unfold gramOf
  rw [← submatrix_mul_equiv _ _ _ (blockEquiv p q), ← submatrix_mul_equiv _ _ _ (blockEquiv p q),
    conjTranspose_submatrix, submatrix_submatrix, submatrix_submatrix, submatrix_diagonal_equiv]
  simp only [Equiv.symm_comp_self, submatrix_id_id]
  congr 2
  ext (i | i) (j | j) <;> simp [diagonal_apply, sigForm, blockEquiv, one_apply] <;> split_ifs <;> simp

theorem exists_periodMatrix {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {p q : ℕ} {B : Set X} (hB : IsOpen B)
    {u₀ : X} (hu₀ : u₀ ∈ B) {A : X → Matrix (Fin p) (Fin q ⊕ Fin p) ℂ} {Bm : X → Matrix (Fin q) (Fin q ⊕ Fin p) ℂ}
    (hA : HolM B A) (hBm : HolM B Bm) {Go : X → Matrix (Fin q) (Fin q) ℂ} {Gw : X → Matrix (Fin p) (Fin p) ℂ}
    (hGo : ∀ u ∈ B, (Go u).PosDef) (hGw : ∀ u ∈ B, (Gw u).PosDef) {Ψ : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ}
    (hΨ : ∀ u ∈ B, Ψ = (A u)ᴴ * Gw u * A u - ((Bm u)ᴴ * Go u * Bm u)ᵀ)
    (hM : (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)).det ≠ 0) :
    ∃ (B' : Set X) (Pi : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsOpen B' ∧ u₀ ∈ B' ∧ B' ⊆ B ∧ HolM B' Pi ∧
      (∀ u ∈ B', IsPeriodGram p (Pi u)
        ((fromBlocks (Go u)ᵀ⁻¹ 0 0 (Gw u)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm)) ∧
      ∀ v : X, (∀ a b : Fin (p + q), p + q - p ≤ (a : ℕ) → (b : ℕ) < p + q - p → ((Pi u₀)⁻¹ * dM Pi u₀ v) a b = 0) →
        ∀ (α : Matrix (Fin p) (Fin p) ℂ) (β : Matrix (Fin p) (Fin q) ℂ),
          dM A u₀ v = α * A u₀ + β * (Bm u₀).map (starRingEnd ℂ) → β = 0 := by
  classical
  have hinl : ∀ i : Fin q, ((blockEquiv p q (Sum.inl i) : Fin (p + q)) : ℕ) = i := by
    intro i
    simp [blockEquiv]
  have hinr : ∀ i : Fin p, ((blockEquiv p q (Sum.inr i) : Fin (p + q)) : ℕ) = q + i := by
    intro i
    simp [blockEquiv]
    omega
  obtain ⟨R1, hR1, hR1d⟩ := exists_sqrt ((hGo u₀ hu₀).transpose)
  obtain ⟨R2, hR2, hR2d⟩ := exists_sqrt (hGw u₀ hu₀)
  have hPsi : ∀ x ∈ B, Ψ = (fromRows ((Bm x).map (starRingEnd ℂ)) (A x))ᴴ *
      fromBlocks (-(Go x)ᵀ) 0 0 (Gw x) * fromRows ((Bm x).map (starRingEnd ℂ)) (A x) :=
    fun x hx => (hΨ x hx).trans (sub_transpose_eq_fromRows_conj_fromBlocks _ _ _ _)
  have hGoTd : ∀ x ∈ B, ((Go x)ᵀ).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hGo x hx).transpose.isUnit).ne_zero
  have hGwd : ∀ x ∈ B, (Gw x).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hGw x hx).isUnit).ne_zero
  have hDd : ∀ x ∈ B, (fromBlocks (-(Go x)ᵀ) 0 0 (Gw x)).det ≠ 0 := by
    intro x hx
    rw [det_fromBlocks_zero₂₁, det_neg]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hGoTd x hx)) (hGwd x hx)
  have hΨd : Ψ.det ≠ 0 := by
    rw [hPsi u₀ hu₀, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hM) (hDd u₀ hu₀)) hM
  have hNd : ∀ x ∈ B, (fromRows ((Bm x).map (starRingEnd ℂ)) (A x)).det ≠ 0 := by
    intro x hx h0
    apply hΨd
    rw [hPsi x hx, det_mul, h0, mul_zero]
  let Q1f : X → Matrix (Fin q ⊕ Fin p) (Fin q) ℂ := fun x => -Ψ⁻¹ * (Bm x)ᵀ
  have hQ1 : ∀ x ∈ B, fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q1f x =
      fromRows ((Go x)ᵀ⁻¹) (0 : Matrix (Fin p) (Fin q) ℂ) :=
    fun x hx => fromRows_mul_neg_inv_mul_transpose _ _ _ _ _ (hGoTd x hx) (hNd x hx) hΨd (hPsi x hx)
  have hAQ1 : ∀ x ∈ B, A x * Q1f x = 0 := by
    intro x hx
    have h1 := hQ1 x hx
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).2
  have hBQ1 : ∀ x ∈ B, (Bm x).map (starRingEnd ℂ) * Q1f x = (Go x)ᵀ⁻¹ := by
    intro x hx
    have h1 := hQ1 x hx
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).1
  have hQ1h : HolM B Q1f := (HolM.const B (-Ψ⁻¹)).mul (fun i j => hBm j i)
  have hMu : IsUnit (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)).det := isUnit_iff_ne_zero.mpr hM
  let C : Matrix (Fin q ⊕ Fin p) (Fin p) ℂ := (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀))⁻¹ *
    fromRows (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ)
  have hAC : A u₀ * C = 1 := by
    have h1 : fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀) * C =
        fromRows (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) := by
      simp only [C]
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hMu, Matrix.one_mul]
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).2
  have hACh : HolM B (fun x => A x * C) := hA.mul (HolM.const B C)
  let B' : Set X := {x | x ∈ B ∧ (A x * C).det ≠ 0}
  have hB'o : IsOpen B' := HolM.isOpen_det hACh hB
  have hu₀' : u₀ ∈ B' := ⟨hu₀, by rw [hAC]; simp⟩
  have hB'B : B' ⊆ B := fun x hx => hx.1
  let Q : X → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := fun x => fromCols (Q1f x) (C * (A x * C)⁻¹)
  let T : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ :=
    fromBlocks R1 0 0 R2 * fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)
  have hTJT : Tᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * T = Ψ := by
    have hS : (fromBlocks R1 0 0 R2)ᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0
        (1 : Matrix (Fin p) (Fin p) ℂ) * fromBlocks R1 0 0 R2 = fromBlocks (-(Go u₀)ᵀ) 0 0 (Gw u₀) := by
      rw [hR1, hR2]
      simp [fromBlocks_conjTranspose, fromBlocks_multiply]
    rw [hPsi u₀ hu₀, ← hS]
    simp only [T, conjTranspose_mul, Matrix.mul_assoc]
  let Pi : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
    fun x => (T * Q x).submatrix (blockEquiv p q).symm (blockEquiv p q).symm
  have hQ2h : HolM B' (fun x => C * (A x * C)⁻¹) :=
    (HolM.const B' C).mul (HolM.inv (hACh.mono hB'B) (fun x hx => hx.2))
  have hQh : HolM B' Q := by
    intro a b
    rcases b with b | b
    · exact (hQ1h.mono hB'B) a b
    · exact hQ2h a b
  have hTQh : HolM B' (fun x => T * Q x) := (HolM.const B' T).mul hQh
  have hPih : HolM B' Pi := fun a b => hTQh _ _
  have hNQ : ∀ x ∈ B', fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x =
      fromBlocks ((Go x)ᵀ⁻¹) ((Bm x).map (starRingEnd ℂ) * (C * (A x * C)⁻¹)) 0 1 := by
    intro x hx
    have hAQ2 : A x * (C * (A x * C)⁻¹) = 1 := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx.2)]
    simp only [Q]
    rw [mul_fromCols, hQ1 x hx.1, fromRows_mul, hAQ2, fromCols_fromRows_eq_fromBlocks]
  have hQd : ∀ x ∈ B', (Q x).det ≠ 0 := by
    intro x hx h0
    have h1 := congrArg det (hNQ x hx)
    rw [det_mul, h0, mul_zero, det_fromBlocks_zero₂₁, det_one, mul_one] at h1
    have hu : IsUnit ((Go x)ᵀ).det := isUnit_iff_ne_zero.mpr (hGoTd x hx.1)
    exact (isUnit_nonsing_inv_det _ hu).ne_zero h1.symm
  have hTd : T.det ≠ 0 := by
    simp only [T]
    rw [det_mul, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (mul_ne_zero hR1d hR2d) hM
  refine ⟨B', Pi, hB'o, hu₀', hB'B, hPih, ?_, ?_⟩
  · intro x hx
    apply periodGram_of (Pi x) ((Go x)ᵀ⁻¹) (Gw x)
      ((Go x)ᵀ * ((Bm x).map (starRingEnd ℂ) * (C * (A x * C)⁻¹))) ((hGo x hx.1).transpose.inv)
    · apply isUnit_iff_ne_zero.mpr
      simp only [Pi]
      rw [det_submatrix_equiv_self, det_mul]
      exact mul_ne_zero hTd (hQd x hx)
    · simp only [Pi]
      rw [gramOf_sigForm_submatrix_blockEquiv]
      calc (T * Q x)ᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) *
            (T * Q x)
          = (Q x)ᴴ * (Tᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * T) *
            Q x := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = (fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x)ᴴ * fromBlocks (-(Go x)ᵀ) 0 0 (Gw x) *
            (fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x) := by
            rw [hTJT, hPsi x hx.1]
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by
            rw [hNQ x hx]
            exact fromBlocks_conj_inv_eq_conj _ (hGo x hx.1).transpose _ _
  · intro v hv α β hd
    have hnhds : B' ∈ nhds u₀ := hB'o.mem_nhds hu₀'
    have hdTQ : dM (fun x => T * Q x) u₀ v = T * dM Q u₀ v := by
      rw [dM_mul (HolM.const B' T) hQh hnhds,
        dM_const (A := fun _ => T) (C := T) (Filter.Eventually.of_forall fun _ => rfl) v,
        Matrix.zero_mul, zero_add]
    have hdPi : dM Pi u₀ v = (T * dM Q u₀ v).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [← hdTQ]
      rfl
    have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr hTd
    have hPi0 : (Pi u₀)⁻¹ * dM Pi u₀ v =
        ((Q u₀)⁻¹ * dM Q u₀ v).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [hdPi]
      simp only [Pi]
      rw [inv_submatrix_equiv, submatrix_mul_equiv, Matrix.mul_inv_rev, Matrix.mul_assoc,
        ← Matrix.mul_assoc T⁻¹ T, nonsing_inv_mul _ hTu, Matrix.one_mul]
    have hz : ∀ i : Fin p, ∀ j : Fin q, ((Q u₀)⁻¹ * dM Q u₀ v) (Sum.inr i) (Sum.inl j) = 0 := by
      intro i j
      have h1 := hv (blockEquiv p q (Sum.inr i)) (blockEquiv p q (Sum.inl j))
        (by rw [hinr]; omega) (by rw [hinl]; omega)
      rw [hPi0] at h1
      simpa using h1
    have hAQ0 : A u₀ * Q u₀ = fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) := by
      simp only [Q]
      rw [mul_fromCols, hAQ1 u₀ hu₀, ← Matrix.mul_assoc, hAC, inv_one, Matrix.one_mul]
    have hA0 : A u₀ = fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) * (Q u₀)⁻¹ := by
      rw [← hAQ0, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQd u₀ hu₀')), Matrix.mul_one]
    have hsel : ∀ (W : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ) (i : Fin p) (j : Fin q),
        (fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) * W) i j = W (Sum.inr i) j := by
      intro W i j
      simp [mul_apply, Fintype.sum_sum_type, one_apply]
    have hAdQ1 : A u₀ * dM Q1f u₀ v = 0 := by
      ext i j
      rw [hA0, Matrix.mul_assoc, hsel]
      exact hz i j
    have hAQ1d : dM (fun x => A x * Q1f x) u₀ v = 0 :=
      dM_const (C := 0) (Filter.eventually_of_mem (hB.mem_nhds hu₀) (fun x hx => hAQ1 x hx)) v
    rw [dM_mul hA hQ1h (hB.mem_nhds hu₀), hAdQ1, add_zero, hd, Matrix.add_mul, Matrix.mul_assoc,
      hAQ1 u₀ hu₀, Matrix.mul_zero, zero_add, Matrix.mul_assoc, hBQ1 u₀ hu₀] at hAQ1d
    have h2 := congrArg (· * (Go u₀)ᵀ) hAQ1d
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hGoTd u₀ hu₀)), Matrix.mul_one,
      Matrix.zero_mul] at h2
    exact h2

end PositivityTheory.Xgp.c_bm_exists_period
