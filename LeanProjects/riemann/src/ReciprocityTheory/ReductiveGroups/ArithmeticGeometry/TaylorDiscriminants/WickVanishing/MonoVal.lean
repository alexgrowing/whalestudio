import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.MV

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

def MonoValSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (ι : Type) [Fintype ι] (j : ι → Fin d), Function.Injective j →
    ∀ (α : ι →₀ ℕ) (g : PS k 1 d),
      constantCoeff (DpolyOf (addF k d) (fun l => Pi.single (j l) 1) (MvPolynomial.monomial α 1) g) =
        (∏ l, ((α l).factorial : k)) * coeff (∑ l, α l • Finsupp.single ((0 : Fin 1), j l) 1) g

section Pair

variable {k : Type} [CommRing k] {σ : Type}

theorem coeff_iter_pderiv (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv k i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by
  induction c generalizing n g with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv]
    have h1 : n + c • Finsupp.single i 1 + Finsupp.single i 1 = n + (c + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    have h2 : ((n + c • Finsupp.single i 1 : σ →₀ ℕ)) i = n i + c := by simp
    rw [h1, h2, Nat.ascFactorial_succ]
    push_cast
    ring

theorem coeff_fold {ι : Type} (cd : ι → σ) (hc : Function.Injective cd) (m : ι → ℕ) (f : MvPowerSeries σ k) :
    ∀ (L : List ι), L.Nodup → ∀ n : σ →₀ ℕ,
      coeff n (L.foldr (fun l g => (pderiv k (cd l))^[m l] g) f) =
        coeff (n + (L.map fun l => m l • Finsupp.single (cd l) 1).sum) f *
          (L.map fun l => ((n (cd l) + 1).ascFactorial (m l) : k)).prod := by
  intro L
  induction L with
  | nil => intro _ n; simp
  | cons l L ih =>
    intro hnd n
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons, coeff_iter_pderiv, ih hnd.2]
    have hprod : (L.map fun l' => (((n + m l • Finsupp.single (cd l) 1 : σ →₀ ℕ) (cd l') + 1).ascFactorial (m l') : k)).prod
        = (L.map fun l' => ((n (cd l') + 1).ascFactorial (m l') : k)).prod := by
      congr 1
      apply List.map_congr_left
      intro l' hl'
      have hne : cd l ≠ cd l' := fun h => hnd.1 (by rw [hc h]; exact hl')
      simp [Finsupp.single_apply, hne]
    rw [hprod, List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, add_assoc]
    ring

end Pair

section Pair2

variable {k : Type} [CommRing k]

theorem ev_zero {d m n : ℕ} (a : Fin m → Pt k n d) : ev a (0 : PS k m d) = 0 := by
  have h := MvPowerSeries.subst_C (a := fun p : Fin m × Fin d => a p.1 p.2) (0 : k)
  rw [map_zero, map_zero] at h
  exact h

theorem dof_single (d : ℕ) (i : Fin d) :
    (Dof (addF k d) (Pi.single i (1 : k)) : PS k 1 d → PS k 1 d) = pderiv k ((0 : Fin 1), i) := by
  classical
  funext f
  have ev1 : ev (n := 1) ![pt k d 0, 0] (1 : PS k 2 d) = 1 := by
    have h := MvPowerSeries.subst_C (a := fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) (1 : k)
    rw [map_one, map_one] at h
    exact h
  have ev0 : ev (n := 1) ![pt k d 0, 0] (0 : PS k 2 d) = 0 := ev_zero _
  have hinner : ∀ j : Fin d, (∑ i' : Fin d, MvPowerSeries.C ((Pi.single i (1 : k) : Fin d → k) i') *
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i') (addF k d j))) =
      if j = i then 1 else 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · have hd : pderiv k ((1 : Fin 2), j) (addF k d j) = 1 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply]
      rw [hd, ev1, mul_one]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_apply, hji]
    · intro b _ hb
      have hd : pderiv k ((1 : Fin 2), b) (addF k d j) = 0 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply, Ne.symm hb]
      rw [hd, ev0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hD : Dof (addF k d) (Pi.single i (1 : k)) f =
      ∑ j, (if j = i then (1 : PS k 1 d) else 0) * pderiv k ((0 : Fin 1), j) f := by
    simp only [Dof, hinner]
  rw [hD]
  simp [ite_mul, Finset.sum_ite_eq']

end Pair2

theorem monoVal : MonoValSt := by
  intro k _ d ι _ j hj α g
  classical
  by_cases h01 : (1 : k) = 0
  · haveI : Subsingleton k := subsingleton_of_zero_eq_one h01.symm
    exact Subsingleton.elim _ _
  · simp only [DpolyOf, MvPolynomial.support_monomial, if_neg h01, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul, DmonOf, dof_single]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [ite_true, map_one, one_mul]
    have hcd : Function.Injective (fun l : ι => ((0 : Fin 1), j l)) :=
      fun a b h => hj (Prod.mk.inj h).2
    have hf := coeff_fold (k := k) (fun l : ι => ((0 : Fin 1), j l)) hcd α g
      (Finset.univ : Finset ι).toList (Finset.nodup_toList _) 0
    try simp only at hf
    rw [hf]
    simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial, Finset.sum_map_toList,
      Finset.prod_map_toList]
    rw [mul_comm]
    try push_cast
    try rfl

end ReciprocityTheory.ChartRestriction.G.TB.MV
