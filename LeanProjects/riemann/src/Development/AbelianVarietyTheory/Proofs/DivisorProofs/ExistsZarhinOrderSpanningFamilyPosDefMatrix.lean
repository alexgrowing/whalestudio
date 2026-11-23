import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam.SpanFam

def colL (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (quat d)ᵀ 0 ((d : ℤ) • 1)

def colR (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 0 (quat d) 1

theorem colL_mul_transpose {d : ℕ} (hd : 0 < d) : colL d * (colL d)ᵀ = (d : ℤ) • form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colL, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  congr 1
  · rw [transpose_transpose, quat_transpose_mul, h1]; simp [sub_smul, smul_smul]
  · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, transpose_zero, transpose_smul, transpose_one]
  · simp
  · simp [smul_smul]

theorem colR_mul_transpose {d : ℕ} (hd : 0 < d) : colR d * (colR d)ᵀ = form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colR, form, fromBlocks_transpose, fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · rw [quat_mul_transpose, h1]; simp [sub_smul]

def col (d : ℕ) (q : Fin 4 ⊕ Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Sum.elim (fun _ => colL d) (fun _ => colR d) q

def famM (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  col d t.2 * single t.1 t.2 1

theorem famM_apply (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) (p q : Fin 4 ⊕ Fin 4) :
    famM d t p q = if q = t.2 then col d t.2 p t.1 else 0 := by
  unfold famM
  split_ifs with h
  · subst h; simp
  · exact mul_single_apply_of_ne _ _ _ _ _ h _

theorem famM_mem (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : famM d t ∈ ord d := by
  intro i j
  rw [famM_apply]
  obtain ⟨k, q⟩ := t
  split_ifs with h
  · simp only at h
    subst h
    rcases k with k | k
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₁, Matrix.zero_apply]; exact dvd_zero _
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
  · exact dvd_zero _

theorem famM_form_transpose {d : ℕ} (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) :
    famM d t * form d * (famM d t)ᵀ = col d t.2 * single t.1 t.1 (form d t.2 t.2) * (col d t.2)ᵀ := by
  calc famM d t * form d * (famM d t)ᵀ
      = col d t.2 * (single t.1 t.2 1 * form d * single t.2 t.1 1) * (col d t.2)ᵀ := by
        simp only [famM, transpose_mul, transpose_single, Matrix.mul_assoc]
    _ = _ := by rw [single_mul_mul_single, _root_.one_mul, _root_.mul_one]

theorem sum_single_diag' (c : ℤ) : ∑ k : Fin 4 ⊕ Fin 4, single k k c = c • (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h; simp [single_apply]
  · rw [Finset.sum_eq_zero (fun k _ => by rw [single_apply]; exact if_neg (fun hk => h (hk.1.symm.trans hk.2)))]
    simp [Matrix.one_apply, h]

theorem sum_famM {d : ℕ} (hd : 0 < d) :
    ∑ t, famM d t * form d * (famM d t)ᵀ = ((8 * d : ℕ) : ℤ) • form d := by
  simp_rw [famM_form_transpose]
  rw [Fintype.sum_prod_type_right]
  have hq : ∀ q : Fin 4 ⊕ Fin 4, ∑ k : Fin 4 ⊕ Fin 4, col d q * single k k (form d q q) * (col d q)ᵀ
      = form d q q • (col d q * (col d q)ᵀ) := by
    intro q
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_diag', Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  simp_rw [hq]
  rw [Fintype.sum_sum_type]
  simp only [col, Sum.elim_inl, Sum.elim_inr, colL_mul_transpose hd, colR_mul_transpose hd, smul_smul]
  have e1 : ∀ j : Fin 4, form d (Sum.inl j) (Sum.inl j) = 1 := fun j => by simp [form]
  have e2 : ∀ j : Fin 4, form d (Sum.inr j) (Sum.inr j) = d := fun j => by
    simp only [form, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one]
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← add_smul, smul_smul]
  rw [_root_.one_mul, ← add_nsmul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  congr 1

def fam (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : ord d := ⟨famM d t, famM_mem d t⟩

def coef (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : (Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → ℤ
  | Sum.inr m, Sum.inl j => N (Sum.inr m) (Sum.inl j) / d
  | Sum.inl m, Sum.inl j => N (Sum.inl m) (Sum.inl j) - ∑ s, quat d s m * (N (Sum.inr s) (Sum.inl j) / d)
  | Sum.inl m, Sum.inr j => N (Sum.inl m) (Sum.inr j)
  | Sum.inr m, Sum.inr j => N (Sum.inr m) (Sum.inr j) - ∑ s, quat d m s * N (Sum.inl s) (Sum.inr j)

theorem sum_coef_famM {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} (hN : N ∈ ord d) (p q : Fin 4 ⊕ Fin 4) :
    ∑ t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4), coef d N t.1 t.2 * famM d t p q = N p q := by
  simp only [famM_apply, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdiv : ∀ m j, (d : ℤ) * (N (Sum.inr m) (Sum.inl j) / d) = N (Sum.inr m) (Sum.inl j) :=
    fun m j => Int.mul_ediv_cancel' (hN m j)
  rcases q with j | j <;> rcases p with m | m <;>
    simp [Fintype.sum_sum_type, col, colL, colR, coef, Matrix.one_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hdiv, mul_comm]
  all_goals done

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam.SpanFam

theorem span_fam_eq_top {d : ℕ} : Submodule.span ℤ (Set.range (fam d)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  rintro ⟨N, hN⟩
  have hx : (⟨N, hN⟩ : ord d) = ∑ t, coef d N t.1 t.2 • fam d t := by
    apply Subtype.ext
    ext p q
    change N p q = ((∑ t, coef d N t.1 t.2 • fam d t : ord d) : Matrix _ _ ℤ) p q
    rw [← sum_coef_famM hN p q]
    simp only [fam, AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddSubgroupClass.coe_zsmul, Matrix.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem sum_fam_mul_bar {d : ℕ} (hd : 0 < d) :
    ∑ t, fam d t * bar d (fam d t) = ((8 * d : ℕ) : ord d) := by
  apply Subtype.ext
  have h : ∑ t, famM d t * form d * (famM d t)ᵀ * formInv d = ((8 * d : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) := by
    rw [← Finset.sum_mul, sum_famM hd, Matrix.smul_mul, form_mul_formInv hd]
  simp only [fam, bar_coe, Subring.coe_mul, Matrix.mul_assoc] at h ⊢
  simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, bar_coe, Matrix.mul_assoc]
  rw [h]
  simp only [Subring.coe_natCast]
  rw [Nat.cast_smul_eq_nsmul ℤ, nsmul_one]

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam

theorem exists_spanning_family_posDef :
    ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  intro d hd
  let e := Fintype.equivFin ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4))
  refine ⟨_, fun i => SpanFam.fam d (e.symm i), 1, 8 * d, ?_, ?_, by omega, ?_⟩
  · have hc : (fun i => SpanFam.fam d (e.symm i)) = SpanFam.fam d ∘ e.symm := rfl
    rw [hc, e.symm.surjective.range_comp]
    exact SpanFam.span_fam_eq_top
  · rw [transpose_one, Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one.add Matrix.PosDef.one
  · simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← SpanFam.sum_fam_mul_bar hd]
    exact Equiv.sum_comp e.symm (fun t => SpanFam.fam d t * bar d (SpanFam.fam d t))

end GlobalTheory.ZarhinFam
