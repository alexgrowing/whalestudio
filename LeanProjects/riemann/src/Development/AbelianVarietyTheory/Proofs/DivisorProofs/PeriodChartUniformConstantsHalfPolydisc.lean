import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

namespace GlobalTheory.UnifConsts

theorem quad_abs_le {m : Type} [Fintype m] (A : Matrix m m ℝ) (E : ℝ)
    (hE : ∀ j k, |A j k| ≤ E) (x : m → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ E * Fintype.card m * (x ⬝ᵥ x) := by
  have h1 : x ⬝ᵥ A *ᵥ x = ∑ j, ∑ k, x j * A j k * x k := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h1]
  calc |∑ j, ∑ k, x j * A j k * x k| ≤ ∑ j, ∑ k, |x j * A j k * x k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : m, ∑ k : m, (E / 2 * (x j) ^ 2 + E / 2 * (x k) ^ 2) := by
        gcongr with j _ k _
        rw [abs_mul, abs_mul]
        have h2 := hE j k
        have h3 : |x j| * |x k| ≤ ((x j) ^ 2 + (x k) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|x j| - |x k|), sq_abs (x j), sq_abs (x k)]
        have h4 : 0 ≤ |A j k| := abs_nonneg _
        nlinarith [mul_nonneg (abs_nonneg (x j)) (abs_nonneg (x k))]
    _ = E * Fintype.card m * (x ⬝ᵥ x) := by
        have h5 : ∀ j, ∑ k : m, (E / 2 * (x j) ^ 2 + E / 2 * (x k) ^ 2) =
            Fintype.card m * (E / 2 * (x j) ^ 2) + E / 2 * ∑ k, (x k) ^ 2 := by
          intro j
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.mul_sum]
        simp only [h5, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum, dotProduct, sq]
        ring

theorem uniform_posDef {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] {K : Set X}
    (hK : IsCompact K) (F : X → Matrix ι ι ℝ) (hF : ∀ j k, ContinuousOn (fun z => F z j k) K)
    (hP : ∀ z ∈ K, (F z).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ y : ι → ℝ, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ F z *ᵥ y := by
  set S : Set (X × (ι → ℝ)) := K ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hq : ContinuousOn (fun p : X × (ι → ℝ) => p.2 ⬝ᵥ F p.1 *ᵥ p.2) S := by
    simp only [dotProduct, mulVec]
    refine continuousOn_finset_sum _ fun j _ => ?_
    refine ContinuousOn.mul (continuous_apply j |>.comp continuous_snd).continuousOn ?_
    refine continuousOn_finset_sum _ fun k _ => ?_
    refine ContinuousOn.mul ?_ (continuous_apply k |>.comp continuous_snd).continuousOn
    exact (hF j k).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hyy : ∀ y : ι → ℝ, y ⬝ᵥ y ≤ Fintype.card ι * ‖y‖ ^ 2 := by
    intro y
    simp only [dotProduct]
    calc ∑ i, y i * y i ≤ ∑ _i : ι, ‖y‖ ^ 2 := by
          gcongr with i
          have := norm_le_pi_norm y i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (y i), sq_abs (y i)]
      _ = _ := by simp

  have hscale : ∀ z y, y ≠ 0 →
      (‖y‖⁻¹ • y) ⬝ᵥ F z *ᵥ (‖y‖⁻¹ • y) = (‖y‖ ^ 2)⁻¹ * (y ⬝ᵥ F z *ᵥ y) := by
    intro z y _
    simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hmem : ∀ z ∈ K, ∀ y : ι → ℝ, y ≠ 0 → (z, ‖y‖⁻¹ • y) ∈ S := by
    intro z hz y hy
    refine ⟨hz, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.2 hy]
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hq
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hp.2
      simp [h0] at this
    have hm : 0 < p.2 ⬝ᵥ F p.1 *ᵥ p.2 := by
      simpa using (hP p.1 hp.1).dotProduct_mulVec_pos hp2
    have hcard : 0 < (Fintype.card ι : ℝ) := by
      have : Nonempty ι := by
        by_contra hι
        rw [not_nonempty_iff] at hι
        exact hp2 (Subsingleton.elim _ _)
      exact_mod_cast Fintype.card_pos
    refine ⟨(p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι, div_pos hm hcard, fun z hz y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h1 := hmin (hmem z hz y hy)
    simp only [Set.mem_setOf_eq] at h1
    rw [hscale z y hy] at h1
    have hn : 0 < ‖y‖ ^ 2 := by positivity
    have h2 : (p.2 ⬝ᵥ F p.1 *ᵥ p.2) * ‖y‖ ^ 2 ≤ y ⬝ᵥ F z *ᵥ y := by
      rwa [le_inv_mul_iff₀ hn, mul_comm] at h1
    calc (p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι * (y ⬝ᵥ y)
        ≤ (p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι * (Fintype.card ι * ‖y‖ ^ 2) := by
          gcongr; exact hyy y
      _ = (p.2 ⬝ᵥ F p.1 *ᵥ p.2) * ‖y‖ ^ 2 := by field_simp
      _ ≤ _ := h2
  · refine ⟨1, one_pos, fun z hz y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    exact absurd ⟨_, hmem z hz y hy⟩ hne

end GlobalTheory.UnifConsts

namespace GlobalTheory.UnifConsts

noncomputable def blockEquiv (g rk : ℕ) :
    Fin (Fintype.card {j : Fin g // j.val < rk}) ⊕ Fin (Fintype.card {j : Fin g // ¬ j.val < rk})
      ≃ Fin g :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl _)

theorem blockEquiv_inl (g rk : ℕ) (i) : (blockEquiv g rk (Sum.inl i)).val < rk :=
  ((Fintype.equivFin {j : Fin g // j.val < rk}).symm i).2

theorem blockEquiv_inr (g rk : ℕ) (i) : ¬ (blockEquiv g rk (Sum.inr i)).val < rk :=
  ((Fintype.equivFin {j : Fin g // ¬ j.val < rk}).symm i).2

theorem submatrix_blockEquiv {g rk : ℕ} (Y S : Matrix (Fin g) (Fin g) ℝ) (T : ℝ)
    (hY : ∀ j k, Y j k = Y k j) (hS : ∀ j k, (rk ≤ j.val ∨ rk ≤ k.val) → S j k = 0) :
    (Y + T • S).submatrix (blockEquiv g rk) (blockEquiv g rk) =
      fromBlocks
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl) +
          T • S.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))ᵀ
        (Y.submatrix (blockEquiv g rk ∘ Sum.inr) (blockEquiv g rk ∘ Sum.inr)) := by
  ext (i | i) (j | j)
  · simp
  · simp [hS _ _ (Or.inr (not_lt.1 (blockEquiv_inr g rk j)))]
  · simp [hS _ _ (Or.inl (not_lt.1 (blockEquiv_inr g rk i))), hY]
  · simp [hS _ _ (Or.inl (not_lt.1 (blockEquiv_inr g rk i)))]

end GlobalTheory.UnifConsts

namespace GlobalTheory.UnifConsts

theorem dot_self_nonneg {m : Type} [Fintype m] (x : m → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem uniform_consts : ∀ (n a g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z) → IsPeriodChart rk τ₀ B → ∃ T₀ c₁ C₁ M β : ℝ, 0 < T₀ ∧ 0 < c₁ ∧ 0 ≤ M ∧ 0 ≤ β ∧ (∀ i (x : Fin g → ℝ), x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x ≤ β * (x ⬝ᵥ x)) ∧ ∀ z ∈ polydisc n (1 / 2), ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ)).IsSymm ∧ (∀ x, c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) ∧ (∀ x, x ⬝ᵥ ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x ≤ C₁ * (x ⬝ᵥ x)) ∧ ∀ (j k : Fin g) (ξ : Fin n → ℂ), ‖fderiv ℂ (fun x => τ₀ x j k) z ξ‖ ≤ M * ‖ξ‖ := by
  intro n a g rk τ₀ B hS h
  have hopen : IsOpen (polydisc n 1) := by
    simp only [polydisc, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const
  set K := Metric.closedBall (0 : Fin n → ℂ) (1 / 2) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hK1 : K ⊆ polydisc n 1 := fun z hz k =>
    lt_of_le_of_lt ((norm_le_pi_norm z k).trans (mem_closedBall_zero_iff.1 hz)) (by norm_num)
  have hhalf : polydisc n (1 / 2) ⊆ K := fun z hz =>
    mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k => (hz k).le)
  have hcont : ∀ j k, ContinuousOn (fun z => τ₀ z j k) K := fun j k =>
    (h.holo j k).continuousOn.mono hK1

  obtain ⟨E', hE'⟩ := hKc.exists_bound_of_continuousOn (f := fun z => fun j k => τ₀ z j k)
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun k => hcont j k)
  set E := max E' 0
  have hE0 : 0 ≤ E := le_max_right _ _
  have hYE : ∀ z ∈ K, ∀ j k, |(τ₀ z j k).im| ≤ E := fun z hz j k =>
    (abs_im_le_norm _).trans ((norm_le_pi_norm (fun k => τ₀ z j k) k).trans
      ((norm_le_pi_norm (fun j k => τ₀ z j k) j).trans ((hE' z hz).trans (le_max_left _ _))))

  have hcd : ∀ j k, ContinuousOn (fun z => fderiv ℂ (fun x => τ₀ x j k) z) K := fun j k =>
    (((ReciprocityTheory.AnForm.Osgood.osgood n _ _ hopen (h.holo j k)).contDiffOn (n := 1) hopen.uniqueDiffOn).continuousOn_fderiv_of_isOpen hopen le_rfl).mono hK1
  obtain ⟨M', hM'⟩ := hKc.exists_bound_of_continuousOn
    (f := fun z => fun j k => fderiv ℂ (fun x => τ₀ x j k) z)
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun k => hcd j k)

  set M := max M' 0
  have hderiv : ∀ z ∈ K, ∀ (j k : Fin g) (ξ : Fin n → ℂ),
      ‖fderiv ℂ (fun x => τ₀ x j k) z ξ‖ ≤ M * ‖ξ‖ := fun z hz j k ξ =>
    ((fderiv ℂ (fun x => τ₀ x j k) z).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right
      ((norm_le_pi_norm (fun k => fderiv ℂ (fun x => τ₀ x j k) z) k).trans
        ((norm_le_pi_norm (fun j k => fderiv ℂ (fun x => τ₀ x j k) z) j).trans
          ((hM' z hz).trans (le_max_left _ _)))) (norm_nonneg _))

  have hBsymm : ∀ i j k, (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (h.psd i).isHermitian.apply j k
  set S : Matrix (Fin g) (Fin g) ℝ := ∑ i, (B i).map (Int.cast : ℤ → ℝ) with hSdef
  have hSapp : ∀ j k, S j k = ∑ i, (B i j k : ℝ) := fun j k => by
    simp [S, Matrix.sum_apply]
  have hSsymm : ∀ j k, S j k = S k j := fun j k => by
    rw [hSapp, hSapp]; exact Finset.sum_congr rfl fun i _ => (hBsymm i j k).symm
  have hSsupp : ∀ j k, (rk ≤ j.val ∨ rk ≤ k.val) → S j k = 0 := fun j k hjk => by
    rw [hSapp]; simp [h.supp _ j k hjk]
  have hYsymm : ∀ z ∈ polydisc n 1, ∀ j k,
      (τ₀ z).map Complex.im j k = (τ₀ z).map Complex.im k j := fun z hz j k => by
    simp [(h.symm z hz).apply j k]

  set e := blockEquiv g rk
  have hkk : Fintype.card {j : Fin g // j.val < rk} ≤ g :=
    (Fintype.card_subtype_le _).trans (by simp)
  have hll : Fintype.card {j : Fin g // ¬ j.val < rk} ≤ g :=
    (Fintype.card_subtype_le _).trans (by simp)
  have hquad : ∀ (A : Matrix (Fin g) (Fin g) ℝ) (x : Fin g → ℝ),
      (x ∘ e) ⬝ᵥ (A.submatrix e e) *ᵥ (x ∘ e) = x ⬝ᵥ A *ᵥ x := fun A x => by
    rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      comp_equiv_dotProduct_comp_equiv]
  have hnorm : ∀ x : Fin g → ℝ, (x ∘ e) ⬝ᵥ (x ∘ e) = x ⬝ᵥ x := fun x =>
    comp_equiv_dotProduct_comp_equiv _ _ _

  set C₀ : ℝ := E * g
  have hC₀ : 0 ≤ C₀ := by positivity
  have ha_bd : ∀ z ∈ K, ∀ x, |x ⬝ᵥ ((τ₀ z).map Complex.im).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) *ᵥ x|
      ≤ C₀ * (x ⬝ᵥ x) := fun z hz x => by
    refine (quad_abs_le _ E (fun j k => hYE z hz _ _) x).trans ?_
    rw [Fintype.card_fin]
    have := dot_self_nonneg x
    have : (Fintype.card {j : Fin g // j.val < rk} : ℝ) ≤ g := by exact_mod_cast hkk
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hE0) (dot_self_nonneg x)
  have hb_bd : ∀ z ∈ K, ∀ y, (((τ₀ z).map Complex.im).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) *ᵥ y) ⬝ᵥ
      (((τ₀ z).map Complex.im).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) *ᵥ y) ≤ C₀ ^ 2 * (y ⬝ᵥ y) := by
    intro z hz y
    set bM := ((τ₀ z).map Complex.im).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)
    rw [show (bM *ᵥ y) ⬝ᵥ (bM *ᵥ y) = y ⬝ᵥ (bMᵀ * bM) *ᵥ y by
      rw [← mulVec_mulVec, dotProduct_mulVec y, vecMul_transpose]]
    refine (le_abs_self _).trans ((quad_abs_le _ (Fintype.card {j : Fin g // j.val < rk} * E ^ 2)
      ?_ y).trans ?_)
    · intro j k
      rw [mul_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |bMᵀ j i * bM i k| ≤ ∑ _i : Fin (Fintype.card {j : Fin g // j.val < rk}), E ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_mul, sq]
              exact mul_le_mul (hYE z hz _ _) (hYE z hz _ _) (abs_nonneg _) hE0
        _ = _ := by simp
    · rw [Fintype.card_fin]
      have := dot_self_nonneg y
      have h1 : (Fintype.card {j : Fin g // j.val < rk} : ℝ) * Fintype.card {j : Fin g // ¬ j.val < rk}
          ≤ g * g := by exact_mod_cast Nat.mul_le_mul hkk hll
      have h2 : (Fintype.card {j : Fin g // j.val < rk} * E ^ 2 * Fintype.card {j : Fin g // ¬ j.val < rk} : ℝ)
          ≤ C₀ ^ 2 := by
        calc _ = E ^ 2 * ((Fintype.card {j : Fin g // j.val < rk} : ℝ) * Fintype.card {j : Fin g // ¬ j.val < rk}) := by ring
          _ ≤ E ^ 2 * (g * g) := by gcongr
          _ = C₀ ^ 2 := by simp only [C₀]; ring
      gcongr

  have hinjr : Function.Injective (fun i : Fin (Fintype.card {j : Fin g // ¬ j.val < rk}) =>
      (⟨e (Sum.inr i), not_lt.1 (blockEquiv_inr g rk i)⟩ : {j : Fin g // rk ≤ j.val})) :=
    by
    intro i j hij
    have h' := Subtype.ext_iff.1 hij
    simp only at h'
    exact Sum.inr_injective (e.injective h')
  obtain ⟨c₀, hc₀, hdc⟩ := uniform_posDef hKc
    (fun z => ((τ₀ z).map Complex.im).submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))
    (fun j k => Complex.continuous_im.comp_continuousOn (hcont _ _))
    (fun z hz => (h.abelian z (hK1 hz)).submatrix hinjr)

  have hinjl : Function.Injective (fun i : Fin (Fintype.card {j : Fin g // j.val < rk}) =>
      (⟨e (Sum.inl i), blockEquiv_inl g rk i⟩ : {j : Fin g // j.val < rk})) :=
    by
    intro i j hij
    have h' := Subtype.ext_iff.1 hij
    simp only at h'
    exact Sum.inl_injective (e.injective h')
  have hSmap : S = (∑ i, B i).map (Int.cast : ℤ → ℝ) := by
    ext j k; rw [hSapp]; simp [Matrix.sum_apply]
  obtain ⟨b₀, hb₀, hbc⟩ := uniform_posDef (X := Unit) isCompact_univ
    (fun _ => S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) (fun j k => continuousOn_const)
    (fun _ _ => by rw [hSmap]; exact h.toric.submatrix hinjl)

  set T₀ : ℝ := (1 + C₀ + C₀ ^ 2 / c₀) / b₀
  have hT₀ : 0 < T₀ := by positivity
  set c₁ : ℝ := ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹
  have hc₁ : 0 < c₁ := by positivity

  set Es : ℝ := ‖fun j k => S j k‖
  have hSE : ∀ j k, |S j k| ≤ Es := fun j k =>
    (norm_le_pi_norm (fun k => S j k) k).trans (norm_le_pi_norm (fun j k => S j k) j)
  set Eb : ℝ := ‖fun i j k => (B i j k : ℝ)‖
  have hBE : ∀ i j k, |(B i j k : ℝ)| ≤ Eb := fun i j k =>
    (norm_le_pi_norm (fun k => (B i j k : ℝ)) k).trans ((norm_le_pi_norm (fun j k => (B i j k : ℝ)) j).trans
      (norm_le_pi_norm (fun i j k => (B i j k : ℝ)) i))
  refine ⟨T₀, c₁, (E + T₀ * Es) * g, M, Eb * g, hT₀, hc₁, le_max_right _ _, by positivity, ?_, ?_⟩
  · intro i x
    refine (le_abs_self _).trans ((quad_abs_le _ Eb (fun j k => by simpa using hBE i j k) x).trans ?_)
    simp
  intro z hz
  have hzK := hhalf hz
  have hz1 := hK1 hzK
  refine ⟨?_, ?_, ?_, hderiv z hzK⟩
  · refine IsSymm.ext fun j k => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply]
    rw [hYsymm z hz1, hSsymm]
  · intro x
    rw [← hquad, ← hnorm, submatrix_blockEquiv _ _ _ (hYsymm z hz1) hSsupp]
    refine hS _ _ _ _ _ _ C₀ c₀ b₀ hC₀ hc₀ hb₀ ?_ ?_ ?_ (ha_bd z hzK) (hb_bd z hzK) (hdc z hzK)
      (hbc () (Set.mem_univ _)) (x ∘ e)
    · exact IsSymm.ext fun j k => hYsymm z hz1 _ _
    · exact IsSymm.ext fun j k => hYsymm z hz1 _ _
    · exact IsSymm.ext fun j k => hSsymm _ _
  · intro x
    refine (le_abs_self _).trans ((quad_abs_le _ (E + T₀ * Es) (fun j k => ?_) x).trans ?_)
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_apply]
      refine (abs_add_le _ _).trans (add_le_add (hYE z hzK j k) ?_)
      rw [abs_mul, abs_of_pos hT₀]
      exact mul_le_mul_of_nonneg_left (hSE j k) hT₀.le
    · simp

end GlobalTheory.UnifConsts
