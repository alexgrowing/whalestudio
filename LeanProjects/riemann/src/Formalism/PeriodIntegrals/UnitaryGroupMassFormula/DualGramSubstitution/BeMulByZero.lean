import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.HasSubstRen

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem cc_add (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (add l ex x y) = 0 := by
  unfold add pt lg
  exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (by
    rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx, PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero])

theorem ren_be (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ τ : Type} [Finite σ] (r : σ → τ) {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    ren r (be l ex ph x y) = be l ex ph (ren r x) (ren r y) := by
  unfold be phAt
  rw [map_sub, map_sub, ren_psubst r _ (cc_add hex0 hl0 hx hy), ren_psubst r _ hx, ren_psubst r _ hy]
  congr 3
  unfold add pt lg
  rw [ren_psubst r _ (by rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx,
    PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero]), map_add, ren_psubst r _ hx, ren_psubst r _ hy]

theorem mulBy_one (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : mulBy l ex 1 x = x := by
  unfold mulBy
  rw [map_one, one_mul]
  exact PI.FglPhSplit.Wk.pt_lg (⟨l, ex, 0⟩ : PI.FglPhSplit.Dat ℂ_[p]) hl0 hinvl hx

theorem be_mulBy_zero (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} (x : MvPowerSeries σ ℂ_[p])
    {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    be l ex ph (mulBy l ex 0 x) y = 0 :=
  PI.FglPhSplit.Wk.be_mulBy_zero (⟨l, ex, ph⟩ : PI.FglPhSplit.Dat ℂ_[p]) hex0 hph0 hl0 hinvl x hy

theorem gramRhs_dual (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {κ ι : Type} [Fintype κ] [Fintype ι]
    (b b' : ι → κ → ℂ_[p] × ℂ_[p]) (hI : DualIso b b') {n : ℕ} (E : ι ⊕ ι ≃ Fin n)
    (hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e')) :
    GramRhs l ex ph (fun j => Sum.elim b b' (E.symm j)) =
      ∑ e, be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e))) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hdiag : ∀ x : ι ⊕ ι, hP (Sum.elim b b' x) (Sum.elim b b' x) = 0 := by
    rintro (e | e)
    exacts [h1 e e, h2 e e]
  have hXv : ∀ j : Fin n, constantCoeff (Xv j : MvPowerSeries (Fin n) ℂ_[p]) = 0 :=
    fun j => constantCoeff_X j
  have bz : ∀ (x : MvPowerSeries (Fin n) ℂ_[p]) (j : Fin n), be l ex ph (mulBy l ex 0 x) (Xv j) = 0 :=
    fun x j => be_mulBy_zero hex0 hph0 hl0 hinvl x (hXv j)
  have hE' : ∀ e e', ¬ E (Sum.inr e) < E (Sum.inl e') := fun e e' h => lt_asymm h (hE e' e)
  have hmix : ∀ e e', be l ex ph (mulBy l ex (hP (b e) (b' e')).1 (Xv (E (Sum.inl e))))
      (Xv (E (Sum.inr e'))) = if e = e' then be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e'))) else 0 := by
    intro e e'
    rw [h3]
    split_ifs
    · rw [Prod.fst_one, mulBy_one hl0 hinvl (hXv _)]
    · rw [Prod.fst_zero, bz]
  unfold GramRhs
  rw [Finset.sum_eq_zero (fun j _ => by rw [hdiag, Prod.fst_zero, map_zero, zero_mul]), zero_add]
  simp only [Finset.sum_filter]
  rw [← E.sum_comp]
  refine (Finset.sum_congr rfl fun x _ => by rw [← E.sum_comp]).trans ?_
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h1, h2,
    Prod.fst_zero, bz, ite_self, Finset.sum_const_zero, hE, hE', if_true, if_false, hmix, zero_add,
    add_zero, Finset.sum_ite_eq]
  simp

end PI.UnitaryGroupMassFormula.PhDualGram

end
