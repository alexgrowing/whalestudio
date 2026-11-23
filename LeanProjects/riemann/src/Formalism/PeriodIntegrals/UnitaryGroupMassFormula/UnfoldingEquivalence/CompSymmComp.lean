import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.Points

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

theorem atN_map {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by
  have hlt : n + i < n + c := by omega
  have hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i := by
    rw [mem_Ufl] at hw ⊢
    intro l hl
    rw [Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    by_cases hl' : l.1 = n + i
    · rw [if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dif_pos hlt]
      have hle : l = ⟨n + i, hlt⟩ := Fin.ext hl'
      rw [hle, sub_self]
    · rw [if_neg hl', mul_zero, sub_zero]
      exact hw l (by omega)
  have hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1 := by
    have h1 := atN_of_mem (hr.2.2 i)
    have h2 := atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)
    rw [sub_add_cancel] at h2
    rw [h2, h1, atN_eN hlt, zero_add]
  have hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
    rw [map_sub, map_smul, sub_add_cancel]
  rw [hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]

private theorem atN_zero {N : ℕ} (i : ℕ) : PI.UnfoldEquiv.Loc.atN (0 : Fin N → k) i = 0 := by
  have h := atN_smul (0 : k) (0 : Fin N → k) i
  rwa [zero_smul, zero_mul] at h

private theorem eN_eq_zero_of_le {N i : ℕ} (h : N ≤ i) : PI.UnfoldEquiv.Loc.eN k N i = 0 := by
  funext l
  have hl := l.2
  rw [eN_apply, Pi.zero_apply, if_neg (by omega)]

theorem chArg_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by
  have key : ∀ i ∈ Finset.range c,
      PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) =
        PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1))) (n + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hic : i + 1 < c
    · have hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) :=
        h.2.2 (i + 1) (by omega) hic
      have hcoord := atN_map hr hi hu
      have hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) =
          (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) :=
        (sub_add_cancel _ _).symm
      rw [hx, map_add, atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]
    · have hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) := by
        rw [mem_Ufl]
        intro l hl
        exfalso
        have := l.2
        omega
      rw [atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero,
        atN_zero, add_zero]
  simp only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero,
      atN_zero, add_zero]

theorem comp_symm_comp {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.toLinearMap ∘ₗ (r.symm.toLinearMap ∘ₗ y) = y := by
  apply LinearMap.ext
  intro v
  simp

theorem symm_comp_comp {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.symm.toLinearMap ∘ₗ (r.toLinearMap ∘ₗ y) = y := by
  apply LinearMap.ext
  intro v
  simp

theorem unfoldEquiv : UnfoldEquiv := by
  intro k₀ K _ _ _ n' n c psi hpsi wt Φ r g hmem hg xj
  have hmem' : PI.UnfoldEquiv.Loc.R1cond k₀ n c r ∧ PI.UnfoldEquiv.Loc.R1cond k₀ n c r⁻¹ := hmem
  have hr : PI.UnfoldEquiv.Loc.R1cond k₀ n c r := hmem'.1
  have hrs : PI.UnfoldEquiv.Loc.R1cond k₀ n c r.symm := hmem'.2
  have hgs : ∀ v, r.symm (PI.UnfoldEquiv.Loc.inX k₀ n c v) = PI.UnfoldEquiv.Loc.inX k₀ n c (g.symm v) := by
    intro v
    rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]
  have hgg : g.toLinearMap ∘ₗ (g.symm.toLinearMap ∘ₗ xj) = xj := by
    apply LinearMap.ext
    intro v
    simp
  let F : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun t => fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t)
  let G : (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) → (PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀) :=
    fun s => fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s)
  have hF : ∀ t, PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t) = r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t := fun t =>
    fillMatrix_extractFree (Q_map hrs hgs (isFillOf_fillMatrix xj t))
  have hG : ∀ s, PI.UnfoldEquiv.Loc.xx1 xj (G s) = r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) s := fun s => by
    have h1 := Q_map hr hg (isFillOf_fillMatrix (g.symm.toLinearMap ∘ₗ xj) s)
    rw [hgg] at h1
    exact fillMatrix_extractFree h1
  have hbij : Function.Bijective F := by
    refine Function.bijective_iff_has_inverse.mpr ⟨G, fun t => ?_, fun s => ?_⟩
    · show fe (r.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 (g.symm.toLinearMap ∘ₗ xj) (F t)) = t
      rw [hF, comp_symm_comp, extractFree_fillMatrix]
    · show fe (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj (G s)) = s
      rw [hG, symm_comp_comp, extractFree_fillMatrix]
  have hca : ∀ t : PI.UnfoldEquiv.Loc.FC n' (c + 1) n c → k₀, PI.UnfoldEquiv.Loc.chArg (PI.UnfoldEquiv.Loc.xx1 xj t) =
      PI.UnfoldEquiv.Loc.chArg (r.symm.toLinearMap ∘ₗ PI.UnfoldEquiv.Loc.xx1 xj t) + PI.UnfoldEquiv.Loc.n1Arg r := fun t => by
    have h2 := chArg_map hr (Q_map hrs hgs (isFillOf_fillMatrix xj t))
    rwa [comp_symm_comp] at h2
  simp only [PI.UnfoldEquiv.Loc.E1, Fintype.piFinset_univ]
  rw [mul_left_comm (psi _)]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective F hbij _ _ (fun t => ?_)
  rw [hF, hca, neg_add, hpsi]
  ring

end PI.UnfoldEquiv.UnitaryGroupMassFormula
