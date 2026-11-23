import Mathlib
open scoped Matrix

namespace GlobalTheory.TriSqrt

lemma det_eq_prod_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  have hi : Function.Injective (fun j => toLex (Fintype.equivFin α (t j), w j)) := by
    intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  letI : LinearOrder n := LinearOrder.lift' _ hi
  refine Matrix.det_of_upperTriangular fun k l hkl => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hs k l hne
  have hkl' : toLex (Fintype.equivFin α (t l), w l) < toLex (Fintype.equivFin α (t k), w k) := hkl
  simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl'
  omega

lemma det_minor {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') (d : n → ℝ)
    (S : Matrix n n ℂ) (hs : ∀ j j', S j j' ≠ 0 → t j = t j' ∧ w j ≤ w j')
    (p : n → Prop) [DecidablePred p] (hp : ∀ c a, S c a ≠ 0 → p a → p c) :
    ((Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val).det
      = ((∏ c ∈ Finset.univ.filter p, ‖S c c‖ ^ 2 * d c : ℝ) : ℂ) := by
  set T : Matrix {x // p x} {x // p x} ℂ := S.submatrix Subtype.val Subtype.val with hT
  have e : (Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val
      = Tᵀ * ((Matrix.diagonal fun j => ((d j.1 : ℝ) : ℂ)) * T.map (starRingEnd ℂ)) := by
    ext a a'
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hT,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)
      (fun c => S c a * ((d c : ℂ) * (starRingEnd ℂ) (S c a')))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
    have : S c a = 0 := by
      by_contra hne
      exact hc (by simpa using hp c a hne a.2)
    rw [this, zero_mul]
  have hdT : T.det = ∏ c, T c c :=
    det_eq_prod_diag (fun c => t c.1) (fun c => w c.1)
      (fun c c' h1 h2 => Subtype.ext (hinj _ _ h1 h2)) T fun c c' hne => hs _ _ hne
  have hdT' : (T.map (starRingEnd ℂ)).det = (starRingEnd ℂ) T.det := by
    rw [RingHom.map_det]; rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdT', hdT,
    map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_subtype (p := p) (Finset.univ.filter p) (by simp), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have := Complex.mul_conj' (S c c)
  simp only [hT, Matrix.submatrix_apply]
  push_cast
  rw [← this]
  ring

end GlobalTheory.TriSqrt

theorem GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  intro g α _ V _ t w d B S Hm hinj hd hc hS j
  classical
  have hH : ContinuousOn Hm B := continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => hc k l
  have hP : ∀ n : ℕ, ContinuousOn (fun b =>
      ∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < n), ‖S b c c‖ ^ 2 * d c) B := by
    intro n
    have h1 : Continuous fun M : Matrix (Fin g) (Fin g) ℂ =>
        ((M.submatrix (Subtype.val : {c // t c = t j ∧ w c < n} → Fin g) Subtype.val).det).re :=
      Complex.continuous_re.comp (continuous_id.matrix_submatrix _ _).matrix_det
    refine (h1.comp_continuousOn hH).congr fun b hb => ?_
    obtain ⟨-, h2, h3⟩ := hS b hb
    simp only [Function.comp_apply]
    rw [h3, GlobalTheory.TriSqrt.det_minor t w hinj d (S b) h2 (fun c => t c = t j ∧ w c < n), Complex.ofReal_re]
    intro c a hne ha
    obtain ⟨h4, h5⟩ := h2 c a hne
    exact ⟨h4.trans ha.1, by omega⟩
  have hne : ∀ b ∈ B, ∀ c, S b c c ≠ 0 := by
    intro b hb c
    obtain ⟨h1, h2, -⟩ := hS b hb
    rw [GlobalTheory.TriSqrt.det_eq_prod_diag t w hinj _ h2, isUnit_iff_ne_zero] at h1
    exact Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_univ _)
  have hne' : ∀ b ∈ B, (∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < w j),
      ‖S b c c‖ ^ 2 * d c) * d j ≠ 0 := fun b hb =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ =>
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (hne b hb c))) (hd c).ne') (hd j).ne'
  have hins : Finset.univ.filter (fun c => t c = t j ∧ w c < w j + 1)
      = insert j (Finset.univ.filter (fun c => t c = t j ∧ w c < w j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : w c = w j
      · exact Or.inl (hinj _ _ h1 h3)
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨rfl, by omega⟩
      · exact ⟨h1, by omega⟩
  refine (((hP (w j + 1)).div ((hP (w j)).mul continuousOn_const) hne').sqrt).congr fun b hb => ?_
  have h0 := hne' b hb
  simp only [Pi.div_apply, Pi.mul_apply]
  rw [hins, Finset.prod_insert (by simp), mul_assoc, mul_comm (d j), mul_div_assoc, div_self h0, mul_one,
    Real.sqrt_sq (norm_nonneg _)]
