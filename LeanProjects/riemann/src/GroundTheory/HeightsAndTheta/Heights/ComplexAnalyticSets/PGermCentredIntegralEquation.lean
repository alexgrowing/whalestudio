import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace CentredIntegralEquation

theorem exists_monic_map_eq_X_pow {R B K : Type*} [CommRing R] [CommRing B] [Field K] [Algebra R B]
    [Module.Finite R B] (ε : R →+* K) (κ : K →+* R) (hεκ : ∀ c, ε (κ c) = c) (x : B)
    (hx : ∀ c : K, c ≠ 0 → ∀ y : B, IsUnit (algebraMap R B (κ c) + x * y)) :
    ∃ Q : R[X], Q.Monic ∧ aeval x Q = 0 ∧ Q.map ε = X ^ Q.natDegree := by
  classical
  have : Nontrivial R := ε.domain_nontrivial
  obtain ⟨χ, hχm, hχ⟩ := (Algebra.IsIntegral.isIntegral (R := R) x)
  have hne : χ.map ε ≠ 0 := (hχm.map ε).ne_zero
  obtain ⟨u, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (χ.map ε) hne 0
  set a := (χ.map ε).rootMultiplicity 0
  have hu0 : u.coeff 0 ≠ 0 := by
    intro h
    apply hndvd
    rw [dvd_iff_isRoot, IsRoot, ← coeff_zero_eq_eval_zero, h]
  have hεκ' : ε.comp κ = RingHom.id K := RingHom.ext hεκ
  set e := χ - X ^ a * u.map κ with he
  have hemap : e.map ε = 0 := by
    rw [he, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_map, hεκ',
      Polynomial.map_id, hfac]
    simp
  set J : Ideal B := (RingHom.ker ε).map (algebraMap R B)
  have heJ : aeval x e ∈ J := by
    rw [aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [Algebra.smul_def]
    refine J.mul_mem_right _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, ← coeff_map, hemap, coeff_zero]

  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := u.map κ)
  have ht : IsUnit (aeval x (u.map κ)) := by
    have h1 : u.map κ = C (κ (u.coeff 0)) + X * r := by
      rw [← hr, coeff_map]; ring
    rw [h1, map_add, aeval_C, map_mul, aeval_X]
    exact hx _ hu0 _
  have hxa : x ^ a ∈ J := by
    obtain ⟨v, hv⟩ := ht
    have h2 : x ^ a * aeval x (u.map κ) = -aeval x e := by
      have := hχ
      rw [← aeval_def] at this
      rw [show χ = X ^ a * u.map κ + e by rw [he]; ring, map_add, map_mul, map_pow, aeval_X] at this
      linear_combination this
    have h3 : x ^ a = -aeval x e * ↑v⁻¹ := by
      rw [← h2, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [h3]
    exact J.mul_mem_right _ (J.neg_mem heJ)
  set y := x ^ (a + 1)
  have hy : y ∈ J := by
    show x ^ (a + 1) ∈ J
    rw [pow_succ]; exact J.mul_mem_right _ hxa
  have hrange : LinearMap.range (LinearMap.mulLeft R y) ≤ RingHom.ker ε • ⊤ := by
    rintro _ ⟨b, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact J.mul_mem_right b hy
  obtain ⟨q, hqm, -, hqc, hq0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R (LinearMap.mulLeft R y) _ hrange
  have hqy : aeval y q = 0 := by
    have := congrArg (fun f : Module.End R B => f 1) hq0
    rw [show (LinearMap.mulLeft R y) = Algebra.lmul R B y from rfl, aeval_algHom_apply] at this
    simpa using this
  have hqmap : q.map ε = X ^ q.natDegree := by
    conv_lhs => rw [hqm.as_sum]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, add_eq_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : q.natDegree - k ≠ 0 := by have := Finset.mem_range.1 hk; omega
    have : q.coeff k ∈ RingHom.ker ε := Ideal.pow_le_self hk' (hqc k)
    rw [RingHom.mem_ker] at this
    simp [this]
  have hQm : (q.comp (X ^ (a + 1))).Monic := hqm.comp (monic_X_pow _) (by rw [natDegree_X_pow]; omega)
  have hQ : (q.comp (X ^ (a + 1))).map ε = X ^ (q.natDegree * (a + 1)) := by
    rw [Polynomial.map_comp, hqmap, Polynomial.map_pow, Polynomial.map_X, X_pow_comp, ← pow_mul, mul_comm]
  refine ⟨q.comp (X ^ (a + 1)), hQm, ?_, ?_⟩
  · rw [aeval_comp, map_pow, aeval_X]; exact hqy
  · rw [← hQm.natDegree_map ε, hQ, natDegree_X_pow]

open PrimeGermPrimitivePresentation

variable {σ : Type} [Fintype σ]

def germEval (w : σ → ℂ) : holGerms w →+* ℂ := Germ.valueRingHom.comp (holGerms w).subtype

theorem germEval_toGerm (w : σ → ℂ) (u : anFun w) : germEval w (toGerm w u) = u.1 w := rfl

def constGerm (w : σ → ℂ) : ℂ →+* holGerms w where
  toFun c := toGerm w ⟨fun _ => c, analyticAt_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem germEval_constGerm (w : σ → ℂ) (c : ℂ) : germEval w (constGerm w c) = c := rfl

theorem germEval_pull {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (r : holGerms (A w)) :
    germEval w (pull A w r) = germEval (A w) r := by
  conv_rhs => rw [← toGerm_rep r]
  rfl

theorem isUnit_of_germEval_ne_zero {w : σ → ℂ} (s : holGerms w) (hs : germEval w s ≠ 0) : IsUnit s := by
  obtain ⟨u, rfl⟩ := toGerm_surjective w s
  rw [germEval_toGerm] at hs
  have hu : AnalyticAt ℂ u.1 w := u.2
  refine IsUnit.of_mul_eq_one (toGerm w ⟨fun z => (u.1 z)⁻¹, hu.inv hs⟩) ?_
  rw [← map_mul, ← map_one (toGerm w)]
  apply Subtype.ext
  refine Germ.coe_eq.2 ((hu.continuousAt.eventually_ne hs).mono fun z hz => ?_)
  exact mul_inv_cancel₀ hz

theorem toGerm_monic_expr {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (x : anFun w) (n : ℕ)
    (c : Fin n → anFun (A w)) :
    toGerm w (x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ)) =
      toGerm w x ^ n + ∑ j, pull A w (toGerm (A w) (c j)) * toGerm w x ^ (j : ℕ) := by
  simp [map_add, map_sum, map_mul, map_pow, pull_toGerm]

theorem coe_monic_expr {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (x : anFun w) (n : ℕ)
    (c : Fin n → anFun (A w)) :
    ((x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ) : anFun w) : (σ → ℂ) → ℂ) =
      fun z => x.1 z ^ n + ∑ j, (c j).1 (A z) * x.1 z ^ (j : ℕ) := by
  funext z
  simp [compA, Finset.sum_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem proof : CentredIntegralEquation.Statement := by
  classical
  intro σ _ w k p d A hp hcoord hpoly g hg
  set I := holGermIdeal w p
  let _ : Algebra (holGerms (A w)) (holGerms w ⧸ I) := ((Ideal.Quotient.mk I).comp (pull A w)).toAlgebra
  have halg : ∀ r, algebraMap (holGerms (A w)) (holGerms w ⧸ I) r = Ideal.Quotient.mk I (pull A w r) :=
    fun _ => rfl

  have hcl : ∀ (u : anFun w) (f : (σ → ℂ) → ℂ), u.1 = f →
      (Ideal.Quotient.mk I (toGerm w u) = 0 ↔ IsGermCombination w p f) := by
    rintro u f rfl
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact toGerm_mem_iff hp u

  have hev : ∀ (x : anFun w) (n : ℕ) (c : Fin n → anFun (A w)),
      aeval (Ideal.Quotient.mk I (toGerm w x)) (X ^ n + ∑ j : Fin n, C (toGerm (A w) (c j)) * X ^ (j : ℕ)) =
        Ideal.Quotient.mk I (toGerm w (x ^ n + ∑ j, compA A w (c j) * x ^ (j : ℕ))) := by
    intro x n c
    rw [toGerm_monic_expr]
    simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, halg]
  set zc : σ → anFun w := fun i => mkA (fun z => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  set cz : σ → holGerms w ⧸ I := fun i => Ideal.Quotient.mk I (toGerm w (zc i))

  have hint : ∀ i, IsIntegral (holGerms (A w)) (cz i) := by
    intro i
    obtain ⟨n, b, hb, hcomb⟩ := hcoord i
    set c : Fin n → anFun (A w) := fun j => mkA (b j) (hb j)
    refine ⟨X ^ n + ∑ j : Fin n, C (toGerm (A w) (c j)) * X ^ (j : ℕ), ?_, ?_⟩
    · refine monic_X_pow_add (degree_sum_le _ _ |>.trans_lt ?_)
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
      exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.2 j.2)
    · rw [← aeval_def, hev]
      exact (hcl _ _ (coe_monic_expr A w (zc i) n c)).2 hcomb

  have hadj : Algebra.adjoin (holGerms (A w)) (Set.range cz) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, rfl⟩ := toGerm_surjective w s
    obtain ⟨t, a, ha, hcomb⟩ := hpoly u.1 u.2
    set a' : (σ → ℕ) → (Fin d → ℂ) → ℂ := fun m => if m ∈ t then a m else 0
    have ha' : ∀ m, AnalyticAt ℂ (a' m) (A w) := by
      intro m
      by_cases hm : m ∈ t
      · simpa [a', hm] using ha m hm
      · simp only [a', hm, if_false]; exact analyticAt_const
    set v : anFun w := ∑ m ∈ t, compA A w (mkA (a' m) (ha' m)) * ∏ i, zc i ^ m i
    have hv : (u - v).1 = fun z => u.1 z - ∑ m ∈ t, a m (A z) * ∏ i, z i ^ m i := by
      funext z
      simp only [v, AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply,
        Finset.prod_apply, Pi.pow_apply]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      simp [compA, mkA, a', zc, hm]
    have h1 : Ideal.Quotient.mk I (toGerm w u) = Ideal.Quotient.mk I (toGerm w v) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      exact (hcl _ _ hv).2 hcomb
    rw [h1]
    simp only [v, map_sum, map_mul, map_prod, map_pow, ← pull_toGerm]
    refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
    rw [← halg]
    exact Subalgebra.algebraMap_mem _ _
  have : Module.Finite (holGerms (A w)) (holGerms w ⧸ I) := by
    refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, ← hadj]
    exact fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact hint i)

  set gA : anFun w := mkA g hg
  set gcl : holGerms w ⧸ I := Ideal.Quotient.mk I (toGerm w gA)
  set xB := gcl - algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) (g w))
  have hx : ∀ c : ℂ, c ≠ 0 → ∀ y : holGerms w ⧸ I,
      IsUnit (algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) c) + xB * y) := by
    intro c hc y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e : algebraMap (holGerms (A w)) (holGerms w ⧸ I) (constGerm (A w) c) + xB * Ideal.Quotient.mk I t =
        Ideal.Quotient.mk I (pull A w (constGerm (A w) c) +
          (toGerm w gA - pull A w (constGerm (A w) (g w))) * t) := by
      simp only [xB, gcl, halg, map_add, map_mul, map_sub]
    rw [e]
    refine (isUnit_of_germEval_ne_zero _ ?_).map _
    simp only [map_add, map_mul, map_sub, germEval_pull, germEval_constGerm, germEval_toGerm]
    simpa [gA, mkA] using hc
  obtain ⟨Q, hQm, hQ0, hQmap⟩ :=
    exists_monic_map_eq_X_pow (germEval (A w)) (constGerm (A w)) (germEval_constGerm _) xB hx
  have : Nontrivial (holGerms (A w)) := (germEval (A w)).domain_nontrivial
  set F := Q.comp (X - C (constGerm (A w) (g w)))
  have hFm : F.Monic := hQm.comp (monic_X_sub_C _) (by rw [natDegree_X_sub_C]; omega)
  have hF0 : aeval gcl F = 0 := by
    rw [aeval_comp, map_sub, aeval_X, aeval_C]
    exact hQ0
  have hFmap : F.map (germEval (A w)) = (X - C (g w)) ^ Q.natDegree := by
    rw [Polynomial.map_comp, hQmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, germEval_constGerm,
      X_pow_comp]
  have hdeg : F.natDegree = Q.natDegree := by
    rw [← hFm.natDegree_map (germEval (A w)), hFmap, sub_eq_add_neg, ← C_neg, natDegree_pow_X_add_C]
  set n := F.natDegree
  have hrepv : ∀ c : holGerms (A w), (rep c).1 (A w) = germEval (A w) c := fun c => by
    rw [← germEval_toGerm, toGerm_rep]
  refine ⟨n, fun j => (rep (F.coeff j)).1, fun j => (rep (F.coeff j)).2, ?_, fun T => ?_⟩
  · refine (hcl _ _ (coe_monic_expr A w gA n fun j => rep (F.coeff j))).1 ?_
    rw [toGerm_monic_expr]
    simp only [toGerm_rep]
    rw [Fin.sum_univ_eq_sum_range (fun i => pull A w (F.coeff i) * toGerm w gA ^ i) n, ← hF0]
    conv_rhs => rw [hFm.as_sum]
    simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, halg, gcl]
    rfl
  · simp only [hrepv]
    rw [Fin.sum_univ_eq_sum_range (fun i => germEval (A w) (F.coeff i) * T ^ i) n]
    have h := congrArg (eval T) hFmap
    conv_lhs at h => rw [hFm.as_sum]
    have hd : F.natDegree = Q.natDegree := hdeg
    simpa [Polynomial.map_sum, eval_finsetSum, hd, hdeg] using h

end CentredIntegralEquation

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
