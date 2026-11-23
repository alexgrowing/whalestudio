import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertCellLocal

open Matrix GlobalTheory.InertBigCell

variable {K : Type} [Field K] {d : ℕ}

def wM (b : GL (Fin d) K) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K :=
  fromBlocks (b : Matrix (Fin d) (Fin d) K) b b (-(b : Matrix (Fin d) (Fin d) K))

def wMi (b : GL (Fin d) K) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K :=
  (2 : K)⁻¹ • fromBlocks ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (-((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))

lemma two_blocks (h2 : (2 : K) ≠ 0) :
    (2 : K)⁻¹ • fromBlocks (1 + 1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (1 + 1 : Matrix (Fin d) (Fin d) K) = 1 := by
  have : fromBlocks (1 + 1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (1 + 1 : Matrix (Fin d) (Fin d) K) = (2 : K) • fromBlocks (1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) 0 1 := by
    rw [fromBlocks_smul, smul_zero, ← one_add_one_eq_two, add_smul, one_smul]
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul, fromBlocks_one]

lemma wM_mul_wMi (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) : wM b * wMi b = 1 := by
  have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv b
  simp only [wM, wMi, Matrix.mul_smul, fromBlocks_multiply, h1, neg_mul, mul_neg, neg_neg, add_neg_cancel]
  exact two_blocks h2

lemma wMi_mul_wM (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) : wMi b * wM b = 1 := by
  have h1 : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  simp only [wM, wMi, Matrix.smul_mul, fromBlocks_multiply, h1, neg_mul, mul_neg, neg_neg, add_neg_cancel]
  exact two_blocks h2

lemma fromBlocks_mul_fromRows_eq {ι κ : Type} [Fintype ι] (A B C D : Matrix ι ι K) (X Y : Matrix ι κ K) :
    fromBlocks A B C D * fromRows X Y = fromRows (A * X + B * Y) (C * X + D * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]

lemma gram_wM (c : K →+* K) (J : Matrix (Fin d) (Fin d) K) (b : GL (Fin d) K) :
    (wM b)ᵀ * dbl J * (wM b).map c =
      fromBlocks 0 ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c +
          (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)
        ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c +
          (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) 0 := by
  simp only [wM, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_neg,
    Matrix.map_neg _ (map_neg c), Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    neg_neg, Matrix.mul_assoc]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

lemma wMi_diagCols (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) :
    wMi b * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) K) =
      fromRows ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) 0 := by
  rw [wMi, show (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) K) = fromRows 1 1 from rfl, Matrix.smul_mul,
    fromBlocks_mul_fromRows_eq]
  simp only [Matrix.mul_one, Matrix.neg_mul, add_neg_cancel]
  ext (i | i) j
  · simp only [Matrix.smul_apply, fromRows_apply_inl, Matrix.add_apply, smul_eq_mul]
    rw [← two_mul, inv_mul_cancel_left₀ h2]
  · simp only [Matrix.smul_apply, fromRows_apply_inr, Matrix.zero_apply, smul_eq_mul, mul_zero]

lemma toBlocks₁₁_conj (b : GL (Fin d) K) (Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) :
    (wMi b * Y * wM b).toBlocks₁₁ = ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((2 : K)⁻¹ • (Y.toBlocks₁₁ + Y.toBlocks₁₂ + Y.toBlocks₂₁ + Y.toBlocks₂₂)) * (b : Matrix (Fin d) (Fin d) K) := by
  conv_lhs => rw [← fromBlocks_toBlocks Y]
  have hs : ∀ (r : K) (Z : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K), (r • Z).toBlocks₁₁ = r • Z.toBlocks₁₁ := fun _ _ => rfl
  simp only [wM, wMi, hs, Matrix.smul_mul, fromBlocks_multiply, toBlocks_fromBlocks₁₁, Matrix.mul_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.smul_apply]
  congr 1
  abel

lemma intMulVec {ι κ : Type} [Fintype κ] (O : ValuationSubring K) (Y : Matrix ι κ K) (v : κ → K)
    (hY : ∀ i j, Y i j ∈ O) (hv : ∀ j, v j ∈ O) : ∀ i, (Y *ᵥ v) i ∈ O :=
  fun i => sum_mem fun j _ => mul_mem (hY i j) (hv j)

lemma inLat2_wM (O : ValuationSubring K) (b : GL (Fin d) K) (y : Fin d ⊕ Fin d → K) (hy : ∀ i, y i ∈ O) :
    InLat2 O b (wM b *ᵥ y) := by
  have h1 : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    simp only [wM, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_add, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Pi.add_apply, Pi.neg_apply]
  · exact add_mem (hy _) (hy _)
  · exact add_mem (hy _) (neg_mem (hy _))

lemma int_wMi (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O) (z : Fin d ⊕ Fin d → K)
    (hz : InLat2 O b z) : ∀ i, (wMi b *ᵥ z) i ∈ O := by
  intro i
  rw [wMi, Matrix.smul_mulVec, fromBlocks_mulVec, Pi.smul_apply, smul_eq_mul]
  refine mul_mem h2i ?_
  rcases i with i | i <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.neg_mulVec, Pi.neg_apply]
  · exact add_mem (hz.1 i) (hz.2 i)
  · exact add_mem (hz.1 i) (neg_mem (hz.2 i))

lemma int_conj_of_keeps (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O)
    (Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (hQ : ∀ z, InLat2 O b z → InLat2 O b (Q *ᵥ z)) :
    ∀ i j, (wMi b * Q * wM b) i j ∈ O := by
  intro i j
  have he : ∀ k, (Pi.single j (1 : K) : Fin d ⊕ Fin d → K) k ∈ O := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := int_wMi O b h2i _ (hQ _ (inLat2_wM O b _ he)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  exact this

lemma keeps_of_int (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O) (h2 : (2 : K) ≠ 0)
    (Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (hQ : ∀ i j, (wMi b * Q * wM b) i j ∈ O) :
    ∀ z, InLat2 O b z → InLat2 O b (Q *ᵥ z) := by
  intro z hz
  have h := inLat2_wM O b _ (intMulVec O _ _ hQ (int_wMi O b h2i z hz))
  have e : wM b * (wMi b * Q * wM b) * wMi b = Q := by
    simp only [← Matrix.mul_assoc, wM_mul_wMi b h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, wM_mul_wMi b h2, Matrix.mul_one]
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e] at h

lemma conj_form (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi Q D : Matrix n n K) (h1 : W * Wi = 1) :
    (Wi * Q * W)ᵀ * (Wᵀ * D * W.map c) * (Wi * Q * W).map c = Wᵀ * (Qᵀ * D * Q.map c) * W.map c := by
  have e1 : ∀ X : Matrix n n K, Wiᵀ * (Wᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have e2 : ∀ X : Matrix n n K, W.map c * (Wi.map c * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero c) (map_one c), Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc, e1, e2]

lemma conj_form' (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi U D : Matrix n n K) :
    (W * U * Wi)ᵀ * D * (W * U * Wi).map c = Wiᵀ * (Uᵀ * (Wᵀ * D * W.map c) * U.map c) * Wi.map c := by
  simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]

lemma back_form (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi D : Matrix n n K) (h1 : W * Wi = 1) :
    Wiᵀ * (Wᵀ * D * W.map c) * Wi.map c = D := by
  have e1 : ∀ X : Matrix n n K, Wiᵀ * (Wᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have e2 : W.map c * Wi.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.mul_assoc, e1, e2, Matrix.mul_one]

lemma intU (O : ValuationSubring K) (X : Matrix (Fin d) (Fin d) K) (hX : ∀ i j, X i j ∈ O) :
    ∀ i j, (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) i j ∈ O := by
  rintro (i | i) (j | j) <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply,
      Matrix.zero_apply]
  · split_ifs <;> simp
  · exact hX i j
  · exact zero_mem O
  · split_ifs <;> simp

end GlobalTheory.InertCellLocal

theorem GlobalTheory.InertCellLocal.bigCell_local_step : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {K : Type} [Field K] (O : ValuationSubring K) (c : K →+* K), (∀ x, c (c x) = x) → (∀ x ∈ O, c x ∈ O) → (2 : K)⁻¹ ∈ O → (2 : K) ≠ 0 →
  ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) K), Jᵀ = -J.map c →
  ∀ (b : GL (Fin d) K) (δ : K), c δ = δ →
  (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) i j ∈ O) →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det ≠ 0 →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det⁻¹ ∈ O →
  ∀ M M' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, M * M' = 1 → Mᵀ * dbl J * M.map c = dbl J →
  (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (M *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (M' *ᵥ z)) →
  ∃ P P' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, P * P' = 1 ∧ Pᵀ * dbl J * P.map c = dbl J ∧
    P * diagCols (Fin d) = diagCols (Fin d) ∧
    (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (P *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (P' *ᵥ z)) ∧
    ∃ N : Matrix (Fin d) (Fin d) K,
      N * ((2 : K)⁻¹ • ((P * M).toBlocks₁₁ + (P * M).toBlocks₁₂ + (P * M).toBlocks₂₁ + (P * M).toBlocks₂₂)) = 1 ∧
      ∀ u, GlobalTheory.InertBigCell.InLat O b u → GlobalTheory.InertBigCell.InLat O b (N *ᵥ u) := open Matrix GlobalTheory.InertBigCell GlobalTheory.InertCellLocal in by
  intro H K _ O c hc hcO h2i h2 d J hJ b δ hδ hG hdet hdeti M M' hMM' hMu hMl

  obtain ⟨cO, hcO'⟩ : ∃ cO : O →+* O, ∀ x, O.subtype (cO x) = c (O.subtype x) :=
    ⟨(c.comp O.subtype).codRestrict O (fun x => hcO x x.2), fun _ => rfl⟩
  have hcOi : ∀ x, cO (cO x) = x := fun x => Subtype.ext (by
    have := hcO' (cO x); rw [hcO' x] at this; exact this.trans (hc _))
  have inj : ∀ {ι κ : Type} {Y Z : Matrix ι κ O}, Y.map O.subtype = Z.map O.subtype → Y = Z :=
    fun h => Matrix.map_injective (fun x y hxy => Subtype.ext hxy) h
  have lift : ∀ {ι κ : Type} (Y : Matrix ι κ K), (∀ i j, Y i j ∈ O) → ∃ Y' : Matrix ι κ O, Y'.map O.subtype = Y :=
    fun Y hY => ⟨fun i j => ⟨Y i j, hY i j⟩, rfl⟩
  have mapc : ∀ {ι κ : Type} (Y : Matrix ι κ O), (Y.map cO).map O.subtype = (Y.map O.subtype).map c := by
    intro ι κ Y; ext i j; simp only [Matrix.map_apply, hcO']
  have hcc : ∀ {ι κ : Type} (Y : Matrix ι κ K), (Y.map c).map c = Y := by
    intro ι κ Y; ext i j; simp only [Matrix.map_apply, hc]
  have smap : ∀ {ι κ : Type} (r : K) (Y : Matrix ι κ K), (r • Y).map c = c r • Y.map c := by
    intro ι κ r Y; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hWW := wM_mul_wMi b h2
  have hWiW := wMi_mul_wM b h2

  obtain ⟨SO, hSO⟩ := lift _ hG
  have hSOdet : IsUnit SO.det := by
    have e : (SO.det : K) = (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det := by
      rw [← hSO]; exact RingHom.map_det O.subtype SO
    have h1 : SO.det * ⟨_, hdeti⟩ = 1 := Subtype.ext (by
      show (SO.det : K) * _ = 1
      rw [e, mul_inv_cancel₀ hdet])
    exact ⟨⟨SO.det, ⟨_, hdeti⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hGc : ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c).map c =
      ((b : Matrix (Fin d) (Fin d) K).map c)ᵀ * J.map c * (b : Matrix (Fin d) (Fin d) K) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hcc]
  have hSK : (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c))ᵀ =
      -(δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).map c := by
    rw [smap, hGc, hδ, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ]
    simp only [Matrix.neg_mul, Matrix.mul_neg, smul_neg, Matrix.mul_assoc]
  have hSOskew : SOᵀ = -SO.map cO := inj (by
    rw [Matrix.map_neg _ (map_neg O.subtype), mapc, Matrix.transpose_map, hSO, hSK])

  have hMl1 := int_conj_of_keeps O b h2i M (fun z hz => (hMl z hz).1)
  have hMl2 := int_conj_of_keeps O b h2i M' (fun z hz => (hMl z hz).2)
  obtain ⟨g, hg⟩ := lift _ hMl1
  obtain ⟨g', hg'⟩ := lift _ hMl2
  have hgg' : g * g' = 1 := inj (by
    rw [Matrix.map_mul, hg, hg', Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype),
      show wMi b * M * wM b * (wMi b * M' * wM b) = wMi b * (M * (wM b * wMi b) * M') * wM b by
        simp only [Matrix.mul_assoc],
      hWW, Matrix.mul_one, hMM', Matrix.mul_one, hWiW])
  have hdetg : IsUnit g.det := Matrix.isUnit_det_of_right_inverse hgg'
  have hgram := gram_wM c J b
  have hFK : fromBlocks (0 : Matrix (Fin d) (Fin d) K)
      (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c))
      (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) 0 =
      ((2 : K)⁻¹ * δ) • ((wM b)ᵀ * dbl J * (wM b).map c) := by
    rw [hgram, fromBlocks_smul, smul_zero, ← two_smul K, smul_smul, show (2 : K)⁻¹ * δ * 2 = δ by field_simp]
  have hunitK : (wMi b * M * wM b)ᵀ * ((wM b)ᵀ * dbl J * (wM b).map c) * (wMi b * M * wM b).map c =
      (wM b)ᵀ * dbl J * (wM b).map c := by
    rw [conj_form c (wM b) (wMi b) M (dbl J) hWW, hMu]
  have hunitO : gᵀ * fromBlocks 0 SO SO 0 * g.map cO = fromBlocks 0 SO SO 0 := inj (by
    rw [Matrix.map_mul, Matrix.map_mul, mapc, Matrix.transpose_map, fromBlocks_map,
      Matrix.map_zero _ (map_zero O.subtype), hg, hSO, hFK, Matrix.mul_smul, Matrix.smul_mul, hunitK])
  have h2O : IsUnit (2 : O) := by
    have h1 : (2 : O) * ⟨_, h2i⟩ = 1 := Subtype.ext (by
      show ((2 : O) : K) * 2⁻¹ = 1
      rw [show ((2 : O) : K) = 2 from rfl, mul_inv_cancel₀ h2])
    exact ⟨⟨2, ⟨_, h2i⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  obtain ⟨XO, hXadm, hXdet⟩ := H cO hcOi h2O SO hSOdet hSOskew g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂
    (by rwa [fromBlocks_toBlocks]) (by rw [fromBlocks_toBlocks]; exact hunitO)

  obtain ⟨X, hX⟩ : ∃ X, XO.map O.subtype = X := ⟨_, rfl⟩
  have hXint : ∀ i j, X i j ∈ O := by rw [← hX]; intro i j; exact (XO i j).2
  have hadm : Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c = 0 := by
    have hK : Xᵀ * (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) + (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) * X.map c = 0 := by
      have := congrArg (fun Y => Y.map O.subtype) hXadm
      rwa [Matrix.map_add _ (map_add O.subtype), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, mapc, hX, hSO,
        Matrix.map_zero _ (map_zero O.subtype)] at this
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; ext i; exact i.elim0
    · have hδ0 : δ ≠ 0 := by
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        rintro rfl; apply hdet; rw [zero_smul]; exact Matrix.det_zero
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hK
      exact (smul_eq_zero.mp hK).resolve_left hδ0
  have hUU : (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) * fromBlocks 1 (-X) 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp
  have hUform : (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K)ᵀ * ((wM b)ᵀ * dbl J * (wM b).map c) *
      (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K).map c = (wM b)ᵀ * dbl J * (wM b).map c := by
    rw [hgram, fromBlocks_transpose, fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c),
      Matrix.map_zero _ (map_zero c), fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    congr 1
    have e : ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c + (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c + Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c + (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) =
        (Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c) +
          (Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
    rw [e, hadm, add_zero]

  have hBBi : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv b
  have hBiB : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  refine ⟨wM b * fromBlocks 1 X 0 1 * wMi b, wM b * fromBlocks 1 (-X) 0 1 * wMi b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show wM b * fromBlocks 1 X 0 1 * wMi b * (wM b * fromBlocks 1 (-X) 0 1 * wMi b) =
        wM b * (fromBlocks 1 X 0 1 * (wMi b * wM b) * fromBlocks 1 (-X) 0 1) * wMi b by simp only [Matrix.mul_assoc],
      hWiW, Matrix.mul_one, hUU, Matrix.mul_one, hWW]
  · rw [conj_form', hUform, back_form c _ _ _ hWW]
  · have key : wM b * fromBlocks 1 X 0 1 * wMi b * @diagCols K _ (Fin d) _ = @diagCols K _ (Fin d) _ := by
      rw [show wM b * fromBlocks 1 X 0 1 * wMi b * @diagCols K _ (Fin d) _ =
          wM b * ((fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) * (wMi b * @diagCols K _ (Fin d) _)) by
            simp only [Matrix.mul_assoc],
        wMi_diagCols b h2, fromBlocks_mul_fromRows_eq]
      simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [← wMi_diagCols b h2, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
    exact key
  · have hc1 : ∀ Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, wMi b * (wM b * Y * wMi b) * wM b = Y := by
      intro Y; simp only [← Matrix.mul_assoc, hWiW, Matrix.one_mul]; rw [Matrix.mul_assoc, hWiW, Matrix.mul_one]
    intro z hz
    refine ⟨keeps_of_int O b h2i h2 _ ?_ z hz, keeps_of_int O b h2i h2 _ ?_ z hz⟩
    · rw [hc1]; exact intU O X hXint
    · rw [hc1]; exact intU O (-X) (fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hXint i j))
  · have hPM : wMi b * (wM b * fromBlocks 1 X 0 1 * wMi b * M) * wM b = fromBlocks 1 X 0 1 * (wMi b * M * wM b) := by
      simp only [← Matrix.mul_assoc, hWiW, Matrix.one_mul]
    have hgb : g.map O.subtype = fromBlocks (g.toBlocks₁₁.map O.subtype) (g.toBlocks₁₂.map O.subtype)
        (g.toBlocks₂₁.map O.subtype) (g.toBlocks₂₂.map O.subtype) := by
      rw [← fromBlocks_map, fromBlocks_toBlocks]
    have hblk := toBlocks₁₁_conj b (wM b * fromBlocks 1 X 0 1 * wMi b * M)
    rw [hPM, ← hg, hgb, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at hblk
    have hEK : (g.toBlocks₁₁ + XO * g.toBlocks₂₁).map O.subtype =
        1 * g.toBlocks₁₁.map O.subtype + X * g.toBlocks₂₁.map O.subtype := by
      rw [Matrix.map_add _ (map_add O.subtype), Matrix.map_mul, hX, Matrix.one_mul]
    have hE1 : (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹ * (g.toBlocks₁₁ + XO * g.toBlocks₂₁) = 1 :=
      Matrix.nonsing_inv_mul _ hXdet
    have hEinv : ∀ Y : Matrix (Fin d) (Fin d) K, (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype *
        ((g.toBlocks₁₁ + XO * g.toBlocks₂₁).map O.subtype * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype),
        Matrix.one_mul]
    have e1 : ∀ Y : Matrix (Fin d) (Fin d) K, ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((b : Matrix (Fin d) (Fin d) K) * Y) = Y := by
      intro Y; rw [← Matrix.mul_assoc, hBiB, Matrix.one_mul]
    refine ⟨(b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), ?_, ?_⟩
    · have hQ : ∀ Q : Matrix (Fin d) (Fin d) K, Q = (b : Matrix (Fin d) (Fin d) K) * (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * Q * (b : Matrix (Fin d) (Fin d) K)) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        intro Q; simp only [← Matrix.mul_assoc, hBBi, Matrix.one_mul]; rw [Matrix.mul_assoc, hBBi, Matrix.mul_one]
      rw [hQ ((2 : K)⁻¹ • _), ← hblk, ← hEK]
      simp only [Matrix.mul_assoc, e1, hEinv, hBBi]
    · intro u hu i
      show (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (((b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *ᵥ u)) i ∈ O
      rw [Matrix.mulVec_mulVec, show ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
          (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) by
        simp only [← Matrix.mul_assoc, hBiB, Matrix.one_mul], ← Matrix.mulVec_mulVec]
      exact intMulVec O _ _ (fun i j => ((g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹ i j).2) hu i
