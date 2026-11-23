import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Vertical

noncomputable section

namespace SecFiniteUnit

theorem prod_natDegree_coeff {R ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R)
    (D : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ D i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, D i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, D i) = ∏ i ∈ s, (f i).coeff (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le_of_le ha' h1,
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1, h2]⟩

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}

def lineSub (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial R :=
  Fin.cases (motive := fun _ => Polynomial R)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def lineTop (y : Par e n → R) (ij : Fin (e + 1) × Fin n) : R :=
  Fin.cases (motive := fun _ => R) (y (.inr ij.2)) (fun i => y (.inl (i, ij.2))) ij.1

theorem lineSub_natDegree_le (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).natDegree ≤ groupWeight (e + 1) n ij 0 := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · split_ifs <;> simp
  | succ i => simp [lineSub]

theorem lineSub_coeff (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineSub y m ij).coeff (groupWeight (e + 1) n ij 0) = lineTop y ij := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    simp only [lineSub, lineTop, Fin.cases_zero, groupWeight, Pi.single_eq_same]
    split_ifs <;> simp [Polynomial.coeff_one]
  | succ i => simp [lineSub, lineTop, groupWeight, Fin.succ_ne_zero]

theorem weight_sum {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    {d : Fin (e + 1) × Fin n →₀ ℕ} (hd : coeff d g ≠ 0) :
    ∑ ij, d ij * groupWeight (e + 1) n ij 0 = δ := by
  have h := congrFun (hg hd) 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simpa [Finset.sum_apply, smul_eq_mul] using h

theorem lineSub_aeval {δ : ℕ} {g : MvPolynomial (Fin (e + 1) × Fin n) k} (hg : IsMultiHomog δ g)
    (y : Par e n → R) (m : Fin n) :
    (aeval (lineSub y m) g).natDegree ≤ δ ∧
      (aeval (lineSub y m) g).coeff δ =
        eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) := by
  have hprod : ∀ d ∈ g.support, (∏ ij, lineSub y m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij, lineSub y m ij ^ d ij).coeff δ = ∏ ij, lineTop y ij ^ d ij := by
    intro d hd
    have h := prod_natDegree_coeff Finset.univ (fun ij => lineSub y m ij ^ d ij)
      (fun ij => d ij * groupWeight (e + 1) n ij 0)
      (fun ij _ => Polynomial.natDegree_pow_le_of_le _ (lineSub_natDegree_le y m ij))
    rw [weight_sum hg (mem_support_iff.mp hd)] at h
    refine ⟨h.1, h.2.trans (Finset.prod_congr rfl fun ij _ => ?_)⟩
    rw [Polynomial.coeff_pow_of_natDegree_le (lineSub_natDegree_le y m ij), lineSub_coeff]
  rw [aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hprod d hd).1, ?_⟩
  have hspec : eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y) = aeval (lineTop y) g := by
    rw [specRest, eval₂_comp_left, aeval_def]
    congr 1
    · ext a; simp
    · funext ⟨i, j⟩
      induction i using Fin.cases with
      | zero => simp [lineTop]
      | succ i => simp [lineTop]
  rw [hspec, aeval_def, eval₂_eq', Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, (hprod d hd).2]

theorem coord_integral {δ : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → R)
    (hg : IsChowForm Q (e + 1) g) (hδ : IsMultiHomog δ g)
    (hu : IsUnit (eval (fun j => y (.inr j)) (specRest (algebraMap k R) g y))) (m : Fin n) :
    IsIntegral R (secCoord (Q.map (MvPolynomial.map (algebraMap k R))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  set x := secCoord Q' y with hx
  have hC : ∀ a : R, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap R (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k R) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap R (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h
    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap R (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ Vertical.incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices Vertical.incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap R (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
          Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := IncidenceNull.full k n (e + 1) Q g hg
  set P : Polynomial R := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj

  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hdeg, hcoeff⟩ := lineSub_aeval hδ y m
  obtain ⟨u, hu'⟩ := hu
  have hmonic : (Polynomial.C ((u⁻¹ : Rˣ) : R) * P).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one δ
      ((Polynomial.natDegree_C_mul_le _ _).trans hdeg)
      (by rw [Polynomial.coeff_C_mul, hcoeff, ← hu', Units.inv_mul])
  refine ⟨(Polynomial.C ((u⁻¹ : Rˣ) : R) * P) ^ N, hmonic.pow N, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, map_mul, mul_pow, hN, mul_zero]

end SecFiniteUnit

theorem SecFiniteUnit.proof : SecFiniteUnit.Statement := by
  intro k R _ _ _ n e δ Q g y hg hδ hu
  set Q' := Q.map (MvPolynomial.map (algebraMap k R))
  have htop : Algebra.adjoin R (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ R (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective R _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecFiniteUnit.coord_integral Q g y hg hδ hu m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights
