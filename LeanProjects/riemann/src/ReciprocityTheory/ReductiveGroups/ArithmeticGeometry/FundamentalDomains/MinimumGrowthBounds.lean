import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MinimumGrowthBounds

variable {r : ℕ} (X : Data E r)

theorem minimumSq_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.firstMinimumSq x := by
  apply Real.sInf_nonneg
  rintro t ⟨v, _, _, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos (X := X) τ).le (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)

theorem minimumSq_two_sided_bounds {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ}
    (hk1 : 0 ≤ k1) (hk2 : 0 < k2) (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w)
    (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w) :
    k1 * X.firstMinimumSq x ≤ X.firstMinimumSq y ∧ X.firstMinimumSq y ≤ k2 * X.firstMinimumSq x := by
  have hc : ∀ τ, 0 ≤ X.c τ := fun τ => (TwoSidedBoostBounds.c_pos (X := X) τ).le
  have e : ∀ g' : (Fin r → E) → ℝ, (¬ ∃ v ∈ X.Λ, v ≠ 0) → {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g' v} = ∅ := by
    intro g' hne
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, hv, hv', _⟩
    exact hne ⟨v, hv, hv'⟩
  have key1 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 ≤ a → (∀ v, 0 ≤ g v) → (∀ v, a * g v ≤ h v) →
      a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (mul_le_mul_of_nonneg_left (csInf_le hb ⟨v, hv, hv', rfl⟩) ha).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  have key2 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 < a → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ a * h v) →
      sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      rw [← div_le_iff₀' ha]
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      rw [div_le_iff₀' ha]
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (csInf_le hb ⟨v, hv, hv', rfl⟩).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine ⟨key1 _ _ k1 hk1 ?_ ?_, key2 _ _ k2 hk2 ?_ ?_⟩
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left (hlow τ _) (hc τ))
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hy τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_le_mul_of_nonneg_left (hup τ _) (hc τ)).trans_eq (mul_left_comm _ _ _)

theorem sqrt_rpow_le (A : ℝ) {k1 k2 L Ly : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2) (hL : 0 ≤ L)
    (h1 : k1 * L ≤ Ly) (h2 : Ly ≤ k2 * L) :
    Real.sqrt Ly ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * Real.sqrt L ^ (-A) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have hLy : Ly = 0 := le_antisymm (by linarith) (by linarith)
    subst hLy
    simp only [Real.sqrt_zero]
    by_cases hA : A = 0
    · subst hA
      simp
    · rw [Real.zero_rpow (neg_ne_zero.mpr hA), mul_zero]
  · have hs : ∀ z : ℝ, 0 ≤ z → Real.sqrt z ^ (-A) = z ^ (-A / 2) := by
      intro z hz
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
      congr 1
      ring
    have hLy : 0 < Ly := lt_of_lt_of_le (mul_pos hk1 hLpos) h1
    rw [hs Ly hLy.le, hs L hL]
    have hLy_eq : Ly = Ly / L * L := (div_mul_cancel₀ Ly hLpos.ne').symm
    have hs1 : k1 ≤ Ly / L := by
      rw [le_div_iff₀ hLpos]
      exact h1
    have hs2 : Ly / L ≤ k2 := by
      rw [div_le_iff₀ hLpos]
      exact h2
    have hspos : 0 < Ly / L := lt_of_lt_of_le hk1 hs1
    rw [hLy_eq, Real.mul_rpow hspos.le hL]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL _)
    rcases le_total 0 (-A / 2) with hp | hp
    · exact (Real.rpow_le_rpow hspos.le hs2 hp).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hk1 hs1 hp).trans (le_max_left _ _)

theorem nfac_pos (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  have hd : ∀ τ i, dmin X.Gm y τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hy τ).2 i
    rw [h0] at h1
    simp at h1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem growth (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ)
    (hmod : ∀ z ∈ X.dom, X.pnorm la P z ≤ C * X.la1 z ^ (-A)) {x y : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2)
    (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w) (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w)
    {R : ℝ} (hR : X.nfac la x / X.nfac la y ≤ R) :
    ‖P y‖ * X.nfac la x ≤ max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by
  have hny := nfac_pos X la hy
  have hnx := nfac_pos X la hx
  obtain ⟨b1, b2⟩ := minimumSq_two_sided_bounds X hx hy hk1.le (lt_of_lt_of_le hk1 hk12) hlow hup
  have hla : X.la1 y ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A) :=
    sqrt_rpow_le A hk1 hk12 (minimumSq_nonneg X hx) b1 b2
  have hq0 : 0 ≤ X.nfac la x / X.nfac la y := div_nonneg hnx.le hny.le
  have hR0 : 0 ≤ R := le_trans hq0 hR
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hly : 0 ≤ X.la1 y ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPy : ‖P y‖ * X.nfac la y ≤ max C 0 * X.la1 y ^ (-A) :=
    calc ‖P y‖ * X.nfac la y = X.pnorm la P y := rfl
      _ ≤ C * X.la1 y ^ (-A) := hmod y hy
      _ ≤ max C 0 * X.la1 y ^ (-A) := mul_le_mul_of_nonneg_right (le_max_left _ _) hly
  have hny' := hny.ne'
  calc ‖P y‖ * X.nfac la x = (‖P y‖ * X.nfac la y) * (X.nfac la x / X.nfac la y) := by
        field_simp
    _ ≤ (max C 0 * X.la1 y ^ (-A)) * R := mul_le_mul hPy hR hq0 (mul_nonneg hC0 hly)
    _ ≤ (max C 0 * (max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A))) * R := by gcongr
    _ = max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by ring

end MinimumGrowthBounds

end ReciprocityTheory.ChartRestriction.G.FD
