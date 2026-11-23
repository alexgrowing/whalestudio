import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorHeightBound
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem card_support_le {R : Type*} [CommSemiring R] {D N n n' : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) (hu : UDegLE n' Q) :
    Q.support.card ≤
      (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) := by
  classical
  let fx : (UXVar D N →₀ ℕ) → (Fin (D + 2) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i))
  let fu : (UXVar D N →₀ ℕ) → (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))
  have hmaps : ∀ s ∈ Q.support, (fun s => (fx s, fu s)) s ∈
      (Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n') := by
    intro s hs
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
    constructor
    · simpa [fx, xDeg] using hx s hs
    · have := hu s hs
      simp only [fu, Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_option, Option.elim]
      unfold uDeg at this ⊢
      omega
  have hinj : Set.InjOn (fun s => (fx s, fu s)) Q.support := by
    intro s _ t _ hst
    simp only [Prod.mk.injEq] at hst
    ext v
    rcases v with p | i
    · have := congrArg (fun f => f (some p)) hst.2
      simpa [fu] using this
    · have := congrArg (fun f => f i) hst.1
      simpa [fx] using this
  calc Q.support.card ≤ ((Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n')).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = _ := by
      rw [Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
        Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_option, Fintype.card_prod]
      congr 1
      · rw [show D + 2 + n - 1 = n + D + 1 by omega]
        exact Nat.choose_symm_of_eq_add (by omega)
      · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega]
        exact Nat.choose_symm_of_eq_add (by omega)

noncomputable def Ey {D N : ℕ} (y : Fin (N + 1) → ℂ) :
    MvPolynomial (UXVar D N) ℂ →ₐ[ℂ] MvPolynomial (Fin (D + 2) × Fin (N + 1)) ℂ :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))

theorem sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (a : α → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  calc ∑ i ∈ s, a i ≤ |∑ i ∈ s, a i| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ s, a i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (s.card * ∑ i ∈ s, a i ^ 2) := Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _

theorem coeff_Ey_le {D N n n' : ℕ} (R : MvPolynomial (UXVar D N) ℂ) (hx : XHom n R)
    (hu : UDegLE n' R) (y : Fin (N + 1) → ℂ) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    ‖coeff β (Ey y R)‖ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R *
      Real.sqrt ((n + D + 1).choose (D + 1) *
        (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) * (∑ j, ‖y j‖) ^ n := by
  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality _ (Ey y R)).2 β
  set z := ReciprocityTheory.MultiplicativeHeights.torusPoint θ with hzdef
  have hz : ∀ p, ‖z p‖ = 1 := by
    intro p
    simp only [hzdef, ReciprocityTheory.MultiplicativeHeights.torusPoint]
    rw [Complex.norm_exp]
    simp
  set Y := ∑ j, ‖y j‖ with hY
  set pt : UXVar D N → ℂ := fun v => eval z (Sum.elim X (fun i => ∑ j, X (i, j) * C (y j)) v)
    with hpt
  have hev : eval z (Ey y R) = eval pt R := by
    have := congrArg (fun φ => φ R)
      (MvPolynomial.comp_aeval (R := ℂ) (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))
        (aeval z))
    simp only [AlgHom.comp_apply] at this
    calc eval z (Ey y R) = aeval z (Ey y R) := by simp
      _ = _ := this
      _ = eval pt R := by simp [hpt]
  have hpt1 : ∀ p, ‖pt (Sum.inl p)‖ = 1 := fun p => by simp [hpt, hz]
  have hpt2 : ∀ i, ‖pt (Sum.inr i)‖ ≤ Y := by
    intro i
    simp only [hpt, Sum.elim_inr, map_sum, map_mul, eval_X, eval_C]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, hz, one_mul]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono : ∀ α ∈ R.support, ‖∏ v, pt v ^ α v‖ ≤ Y ^ n := by
    intro α hα
    rw [norm_prod, Fintype.prod_sum_type]
    simp only [norm_pow, hpt1, one_pow, Finset.prod_const_one, one_mul]
    calc ∏ i, ‖pt (Sum.inr i)‖ ^ α (Sum.inr i) ≤ ∏ i, Y ^ α (Sum.inr i) :=
          Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt2 i) _
      _ = Y ^ n := by rw [Finset.prod_pow_eq_pow_sum, ← hx α hα]; rfl
  have hcard := card_support_le R hx hu
  calc ‖coeff β (Ey y R)‖ ≤ ‖eval z (Ey y R)‖ := hθ
    _ = ‖∑ α ∈ R.support, coeff α R * ∏ v, pt v ^ α v‖ := by rw [hev, eval_eq']
    _ ≤ ∑ α ∈ R.support, ‖coeff α R‖ * Y ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono α hα) (norm_nonneg _)
    _ = (∑ α ∈ R.support, ‖coeff α R‖) * Y ^ n := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt R.support.card * ReciprocityTheory.MultiplicativeHeights.polyL2 R) * Y ^ n := by
        gcongr
        exact sum_le_sqrt_card_mul _ _
    _ ≤ _ := by
        rw [mul_comm (Real.sqrt _) (ReciprocityTheory.MultiplicativeHeights.polyL2 R)]
        gcongr
        unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity

end ReciprocityTheory.ChartRestriction.G.T0
