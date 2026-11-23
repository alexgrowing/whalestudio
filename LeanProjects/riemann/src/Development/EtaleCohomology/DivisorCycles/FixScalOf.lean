import Development.EtaleCohomology.DivisorCycles.CycleCountPf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalEig

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.ScalarFixedPointsUnderAeval
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem comm_aeval (y p : Mat C N) (h : Commute y p) (Q : C[X]) : Commute (aeval y Q) p := by
  induction Q using Polynomial.induction_on with
  | C a => simpa using Algebra.commute_algebraMap_left a p
  | add f g hf hg => simpa using hf.add_left hg
  | monomial k a _ =>
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    exact (Algebra.commute_algebraMap_left a p).mul_left (h.pow_left _)

theorem aeval_eig (y : Mat C N) (μ : C) (v : Fin N → C) (hv : y *ᵥ v = μ • v) (Q : C[X]) :
    aeval y Q *ᵥ v = Q.eval μ • v :=
  _root_.UpperTheory.Reformulated.B.Qp10.aeval_eig y μ v hv Q

theorem same_fix {n : ℕ} (π : Equiv.Perm (Fin n)) (i a : Fin n) (hi : π i = i) (h : π.SameCycle i a) : a = i := by
  obtain ⟨z, hz⟩ := h
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hi] at hz
  exact hz.symm

theorem kill {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C) (hp : Sys p)
    (hd : Disj y π p)
    (hv : ∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0)
    (i : Fin n) (hi : π i = i) (hyi : Commute y (p i)) (S : Finset (Fin n)) (hS : i ∉ S) :
    ∀ w : Fin N → C, p i *ᵥ w = w → aeval y (∏ j ∈ S, (X - Polynomial.C (l j))) *ᵥ w = 0 → w = 0 := by
  induction S using Finset.induction_on with
  | empty => intro w _ h; simpa using h
  | insert a s ha ih =>
    intro w hw h
    have hai : a ≠ i := fun h' => hS (h' ▸ Finset.mem_insert_self a s)
    have his : i ∉ s := fun h' => hS (Finset.mem_insert_of_mem h')
    rw [Finset.prod_insert ha, map_mul, ← mulVec_mulVec] at h
    by_cases h0 : aeval y (∏ j ∈ s, (X - Polynomial.C (l j))) *ᵥ w = 0
    · exact ih his w hw h0
    exfalso
    set w' := aeval y (∏ j ∈ s, (X - Polynomial.C (l j))) *ᵥ w with hw'
    have heig : y *ᵥ w' = l a • w' := by
      simp only [map_sub, aeval_X, aeval_C, sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec,
        one_mulVec, sub_eq_zero] at h
      exact h
    have hc := comm_aeval y (p i) hyi (∏ j ∈ s, (X - Polynomial.C (l j)))
    have hcond : ∀ k, ¬ π.SameCycle i k → p k *ᵥ w' = 0 := by
      intro k hk
      have hki : k ≠ i := fun h' => hk (h' ▸ Equiv.Perm.SameCycle.refl π i)
      rw [hw', ← hw, mulVec_mulVec, mulVec_mulVec, mul_assoc, hc.eq, ← mul_assoc, hp.1.ortho hki, zero_mul, zero_mulVec]
    obtain ⟨v, hv0, hyv, hvc⟩ := hv a
    exact hd i a (fun h' => hai (same_fix π i a hi h')) (l a) w' v h0 hv0 heig hyv hcond hvc

theorem FixScal_of : LateralTheory.DivDb.CycleCountPf.FixScal := by
  intro C _ _ _ N n p y π l hp hyp hdeg hd hl hv i hi
  obtain ⟨q, hq0, hqd, hqy⟩ := hdeg
  have hroot : ∀ j, q.IsRoot (l j) := by
    intro j
    obtain ⟨v, hv0, hyv, -⟩ := hv j
    have := aeval_eig y (l j) v hyv q
    rw [hqy, zero_mulVec, eq_comm, smul_eq_zero] at this
    exact this.resolve_right hv0
  set s : Multiset C := Multiset.map l Finset.univ.val with hs
  have hnd : s.Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : s ≤ q.roots := (Multiset.le_iff_subset hnd).2 (fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hroot j))
  obtain ⟨r, hr⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hq0 s).2 hle
  set P := (s.map fun a => X - Polynomial.C a).prod with hPdef
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hPd : P.natDegree = n := by
    rw [hPdef, natDegree_multiset_prod_X_sub_C_eq_card, hs, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin]
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (by rw [hr, mul_zero])
  have hrd : r.natDegree = 0 := by
    have := hPm.natDegree_mul' hr0
    rw [← hr, hPd] at this; omega
  have hc0 : r.coeff 0 ≠ 0 := by
    intro h; apply hr0; rw [eq_C_of_natDegree_eq_zero hrd, h, map_zero]
  have hPy : aeval y P = 0 := by
    rw [hr, eq_C_of_natDegree_eq_zero hrd, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, mul_smul_one,
      smul_eq_zero] at hqy
    exact hqy.resolve_left hc0
  have hPP : P = ∏ j, (X - Polynomial.C (l j)) := by
    rw [hPdef, hs, Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
  rw [hPP, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm, map_mul] at hPy
  have hyi : Commute y (p i) := by have := hyp i; rw [hi] at this; exact this
  set M := aeval y (X - Polynomial.C (l i)) with hM
  have hMc : Commute M (p i) := comm_aeval y (p i) hyi _
  have hidem : p i * p i = p i := hp.1.idem i
  have hMp : M * p i = 0 := by
    rw [ext_iff_mulVec]
    intro u
    rw [zero_mulVec]
    apply kill p y π l hp hd hv i hi hyi (Finset.univ.erase i) (Finset.notMem_erase i _)
    · rw [mulVec_mulVec, ← mul_assoc, ← hMc.eq, mul_assoc, hidem]
    · rw [mulVec_mulVec, ← mul_assoc, hPy, zero_mul, zero_mulVec]
  refine ⟨l i, ?_⟩
  rw [hM, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul] at hMp
  exact hMp

end LateralTheory.DivDb.ScalarFixedPointsUnderAeval
