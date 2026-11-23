import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PdAevalScale
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsP
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DPsiMonomialIwh
import Mathlib.LinearAlgebra.Matrix.Transvection
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

private theorem isWeightedHomogeneous_comp_addMonoidHom {R σ M M' : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M'] (ψ : M →+ M') (w : σ → M) {f : MvPolynomial σ R} {m : M} (h : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous (fun v => ψ (w v)) f (ψ m) := by
  intro d hd
  rw [← h hd, Finsupp.weight_apply, Finsupp.weight_apply]
  simp [Finsupp.sum, map_sum, map_nsmul]

private theorem isWeightedHomogeneous_colW_adjugate_genY {R : Type} [CommRing R] (r : ℕ) (a i : Fin r) :
    IsWeightedHomogeneous (colW r r) ((genY R r).adjugate a i) (fun k => if k = a then 0 else 1) := by
  rw [Matrix.adjugate_apply, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  by_cases hs : s a = i
  · have e : (fun k : Fin r => if k = a then (0:ℕ) else 1) = ∑ p : Fin r, (if p = a then 0 else Pi.single p 1) := by
      funext k
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · by_cases hk : k = a <;> simp [hk]
      · intro b _ hb
        by_cases hba : b = a
        · simp [hba]
        · simp [hba, Pi.single_eq_of_ne (Ne.symm hb)]
      · simp
    rw [e]
    apply IsWeightedHomogeneous.prod
    intro p _
    by_cases hp : p = a
    · subst hp; simp [Matrix.updateRow_apply, hs]; exact isWeightedHomogeneous_one _ _
    · have hsp : s p ≠ i := fun h => hp (s.injective (h.trans hs.symm))
      simp only [Matrix.updateRow_apply, hsp, hp, if_false, genY, Matrix.of_apply]
      have := isWeightedHomogeneous_X R (colW r r) (s p, p)
      simpa [colW] using this
  · obtain ⟨p, hp⟩ : ∃ p, s p = i := ⟨s.symm i, by simp⟩
    have hpa : p ≠ a := fun h => hs (h ▸ hp)
    rw [Finset.prod_eq_zero (Finset.mem_univ p)]
    · exact isWeightedHomogeneous_zero _ _ _
    · simp [Matrix.updateRow_apply, hp, Pi.single_apply, hpa]

private theorem isWeightedHomogeneous_colW_detY {R : Type} [CommRing R] (r : ℕ) : IsWeightedHomogeneous (colW r r) (detY R r) (fun _ => 1) := by
  rw [detY_eq, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have e : (fun _ : Fin r => (1:ℕ)) = ∑ p : Fin r, Pi.single p 1 := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e]
  apply IsWeightedHomogeneous.prod
  intro p _
  have := isWeightedHomogeneous_X R (colW r r) (s p, p)
  simpa [genY, colW] using this

private theorem colAdd_mapMatrix_genY_eq_mul_transvection {R : Type} [CommRing R] (r : ℕ) (l j : Fin r) (c : R) :
    (colAdd R l j c).mapMatrix (genY R r) = genY R r * Matrix.transvection l j (C c) := by
  refine Matrix.ext fun a b => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, genY, Matrix.of_apply, colAdd, aeval_X, Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  by_cases hb : b = j
  · subst hb
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · have hb' : j ≠ b := Ne.symm hb
    simp [Matrix.mul_apply, Matrix.single_apply, hb, hb']

private theorem colAdd_detY_eq_of_ne {R : Type} [CommRing R] (r : ℕ) (l j : Fin r) (hlj : l ≠ j) (c : R) :
    colAdd R l j c (detY R r) = detY R r := by
  rw [detY_eq, AlgHom.map_det, colAdd_mapMatrix_genY_eq_mul_transvection, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hlj, mul_one]

private theorem colAdd_adjugate_genY_eq_of_ne {R : Type} [CommRing R] (r : ℕ) (l j : Fin r) (hlj : l ≠ j) (c : R) (a i : Fin r) :
    colAdd R l j c ((genY R r).adjugate a i) = (genY R r).adjugate a i + (if a = l then -(C c) * (genY R r).adjugate j i else 0) := by
  have h1 : colAdd R l j c ((genY R r).adjugate a i) = ((colAdd R l j c).mapMatrix (genY R r).adjugate) a i := rfl
  have hT : (Matrix.transvection l j (C c : MvPolynomial (Fin r × Fin r) R)).adjugate = Matrix.transvection l j (-(C c)) := by
    have hm : Matrix.transvection l j (C c : MvPolynomial (Fin r × Fin r) R) * Matrix.transvection l j (-(C c)) = 1 := by
      rw [Matrix.transvection_mul_transvection_same _ _ hlj, add_neg_cancel, Matrix.transvection_zero]
    calc (Matrix.transvection l j (C c : MvPolynomial (Fin r × Fin r) R)).adjugate
        = (Matrix.transvection l j (C c : MvPolynomial (Fin r × Fin r) R)).adjugate * (Matrix.transvection l j (C c) * Matrix.transvection l j (-(C c))) := by rw [hm, Matrix.mul_one]
      _ = Matrix.transvection l j (-(C c)) := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne _ _ hlj, one_smul, Matrix.one_mul]
  rw [h1, AlgHom.map_adjugate, colAdd_mapMatrix_genY_eq_mul_transvection, Matrix.adjugate_mul_distrib, hT]
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  congr 1
  by_cases ha : a = l
  · subst ha; simp [Matrix.single_mul_apply_same]
  · have ha' : l ≠ a := Ne.symm ha
    simp [ha, ha', Matrix.mul_apply, Matrix.single_apply]

private theorem adjugate_subst_mem_dualWeyl_of_mem {R : Type} [CommRing R] [IsDomain R] [Infinite R] (r : ℕ) (ν : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) (hf : f ∈ dualWeyl R r r ν) :
    aeval (fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) f ∈
      dualWeyl R r r (fun k => ∑ j, if j = k.rev then 0 else ν j) := by
  obtain ⟨hw, hinv⟩ := (dualWeylPoint R r r ν f).mp hf
  rw [dualWeylPoint]
  constructor
  · let ψ : (Fin r → ℕ) →+ (Fin r → ℕ) :=
      { toFun := fun x k => ∑ j, if j = k.rev then 0 else x j
        map_zero' := by funext k; simp
        map_add' := by
          intro x y
          funext k
          simp only [Pi.add_apply, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp }
    have h1 := isWeightedHomogeneous_comp_addMonoidHom ψ (colW r r) hw
    refine isWH_algHom _ (fun v => ψ (colW r r v)) (colW r r) (fun v => ?_) h1
    rw [aeval_X]
    convert isWeightedHomogeneous_colW_adjugate_genY (R := R) r v.2.rev v.1 using 1
    funext k
    show (∑ j, if j = k.rev then 0 else (colW r r v) j) = _
    simp only [colW]
    rw [Finset.sum_eq_single v.2]
    · by_cases hk : k = v.2.rev
      · subst hk; simp
      · have : v.2 ≠ k.rev := fun e => hk (by rw [e, Fin.rev_rev])
        simp [hk, this]
    · intro b _ hb
      split_ifs <;> simp [Pi.single_eq_of_ne hb]
    · simp
  · intro l j hlj c
    have key : (colAdd R l j c).comp (aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) =
        (aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1).comp (colAdd R j.rev l.rev (-c)) := by
      apply MvPolynomial.algHom_ext
      intro v
      rw [AlgHom.comp_apply, AlgHom.comp_apply, aeval_X, colAdd_adjugate_genY_eq_of_ne r l j (ne_of_lt hlj) c]
      simp only [colAdd, aeval_X]
      by_cases h : v.2 = l.rev
      · have h' : v.2.rev = l := by rw [h, Fin.rev_rev]
        simp [h, h', map_add, map_mul, aeval_X, aeval_C, Fin.rev_rev]
      · have h' : v.2.rev ≠ l := fun e => h (by rw [← e, Fin.rev_rev])
        simp [h, h']
    have hl : j.rev < l.rev := Fin.rev_lt_rev.mpr hlj
    calc colAdd R l j c (aeval (fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) f)
        = ((colAdd R l j c).comp (aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1)) f := rfl
      _ = (aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) (colAdd R j.rev l.rev (-c) f) := by rw [key]; rfl
      _ = _ := by rw [hinv _ _ hl]

private theorem detY_mem_dualWeyl_const_one {R : Type} [CommRing R] [IsDomain R] [Infinite R] (r : ℕ) :
    detY R r ∈ dualWeyl R r r (fun _ => 1) :=
  (dualWeylPoint R r r _ _).mpr ⟨isWeightedHomogeneous_colW_detY r, fun l j hlj c => colAdd_detY_eq_of_ne r l j (ne_of_lt hlj) c⟩

private theorem map_aeval_adjugate_subst_eq_aeval_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A) :
    map φ (aeval (fun v : Fin r × Fin r => (genY A r).adjugate v.2.rev v.1) f) =
      aeval (fun v : Fin r × Fin r => (genY B r).adjugate v.2.rev v.1) (map φ f) := by
  have hg : (map φ).mapMatrix (genY A r) = genY B r := by
    refine Matrix.ext fun a b => ?_
    simp [genY]
  have hadj : ∀ a i, map φ ((genY A r).adjugate a i) = (genY B r).adjugate a i := by
    intro a i
    have := RingHom.map_adjugate (map φ) (genY A r)
    rw [hg] at this
    exact congrFun (congrFun this a) i
  induction f using MvPolynomial.induction_on
  next a =>
    simp [aeval_C, map_C]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp, aeval_X, map_X, hadj]

private theorem pow_mul_aeval_eq_of_homogeneous_of_mul_eq {R σ S : Type} [CommRing R] [CommRing S] [Algebra R S] (Z Z' : σ → S) (u w : S)
    (h : ∀ v, u * Z v = w * Z' v) (D : ℕ) (f : MvPolynomial σ R)
    (hf : ∀ d ∈ f.support, (d.sum fun _ k => k) = D) :
    u ^ D * aeval Z f = w ^ D * aeval Z' f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial]
  have hD := hf d hd
  have e1 : u ^ D * d.prod (fun i k => Z i ^ k) = d.prod (fun i k => (u * Z i) ^ k) := by
    rw [← hD]
    simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have e2 : w ^ D * d.prod (fun i k => Z' i ^ k) = d.prod (fun i k => (w * Z' i) ^ k) := by
    rw [← hD]
    simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc u ^ D * (algebraMap R S (coeff d f) * d.prod (fun i k => Z i ^ k))
      = algebraMap R S (coeff d f) * (u ^ D * d.prod (fun i k => Z i ^ k)) := by ring
    _ = algebraMap R S (coeff d f) * (w ^ D * d.prod (fun i k => Z' i ^ k)) := by rw [e1, e2]; simp only [h]
    _ = _ := by ring

private theorem degree_eq_sum_of_mem_dualWeyl {R : Type} [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) :
    ∀ d ∈ f.support, (d.sum fun _ k => k) = ∑ j, ν j := by
  have hw : IsWeightedHomogeneous (colW r n) f ν := by
    simp only [dualWeyl, Submodule.mem_inf, mem_weightedHomogeneousSubmodule] at hf
    exact hf.1
  let ψ : (Fin n → ℕ) →+ ℕ :=
    { toFun := fun x => ∑ j, x j
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib] }
  have h1 := isWeightedHomogeneous_comp_addMonoidHom ψ (colW r n) hw
  intro d hd
  have := h1 (mem_support_iff.mp hd)
  rw [Finsupp.weight_apply] at this
  have hc : ∀ v : Fin r × Fin n, ψ (colW r n v) = 1 := by
    intro v
    simp [ψ, colW]
  simp only [hc, smul_eq_mul, mul_one] at this
  exact this

private theorem transpose_act_comp_adjugate_subst_comp_act_eq_det {R : Type} [CommRing R] (r : ℕ) (A : Matrix (Fin r) (Fin r) R) :
    (rowAct R A.transpose).comp ((aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1).comp (rowAct R A)) =
      aeval fun v : Fin r × Fin r => C A.det * (genY R r).adjugate v.2.rev v.1 := by
  set Am : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) R) := A.transpose.map C with hAmdef
  have hAm : (rowAct R A.transpose).mapMatrix (genY R r) = Am * genY R r := by
    refine Matrix.ext fun a c => ?_
    simp [Am, rowAct, genY, Matrix.mul_apply, aeval_X]
  have hdet : Am.det = C A.det := by
    rw [hAmdef, show A.transpose.map (C : R → MvPolynomial (Fin r × Fin r) R) = (C : R →+* MvPolynomial (Fin r × Fin r) R).mapMatrix A.transpose from rfl, ← RingHom.map_det, Matrix.det_transpose]
  have hr : ∀ a i, rowAct R A.transpose ((genY R r).adjugate a i) = ((genY R r).adjugate * Am.adjugate) a i := by
    intro a i
    have h1 : rowAct R A.transpose ((genY R r).adjugate a i) = ((rowAct R A.transpose).mapMatrix (genY R r).adjugate) a i := rfl
    rw [h1, AlgHom.map_adjugate, hAm, Matrix.adjugate_mul_distrib]
  apply MvPolynomial.algHom_ext
  intro v
  have hx : rowAct R A (X v) = ∑ b, C (A v.1 b) * X (b, v.2) := by simp [rowAct, aeval_X]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hx, map_sum, map_sum, aeval_X]
  have hC : ∀ c : R, rowAct R (n := r) A.transpose (C c) = C c := fun c => (rowAct R (n := r) A.transpose).commutes c
  simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, hC, hr]
  have hsum : (∑ b, C (A v.1 b) * ((genY R r).adjugate * Am.adjugate) v.2.rev b) = ((genY R r).adjugate * Am.adjugate * Am) v.2.rev v.1 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Am, mul_comm]
  rw [hsum, Matrix.mul_assoc, Matrix.adjugate_mul, hdet]
  simp [Matrix.mul_smul, Matrix.smul_apply]

private theorem adjugate_subst_mapMatrix_genY_eq_transpose_mul_antidiag {R : Type} [CommRing R] (r : ℕ) :
    (aeval fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1).mapMatrix (genY R r) =
      (genY R r).adjugate.transpose * (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0).map C := by
  refine Matrix.ext fun i b => ?_
  simp [genY, aeval_X, Matrix.mul_apply, Matrix.transpose_apply]

private theorem antidiagonal_mul_self_eq_one {R : Type} [CommRing R] (r : ℕ) :
    (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0) * (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0) = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev]
  · by_cases h : a = b <;> simp [h, Matrix.one_apply]
  · intro k _ hk; simp [hk]
  · simp

private theorem adjugate_subst_detY_eq_det_antidiag_mul_pow {R : Type} [CommRing R] (r : ℕ) :
    aeval (fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) (detY R r) =
      C (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0).det * detY R r ^ (r - 1) := by
  rw [detY_eq, AlgHom.map_det, adjugate_subst_mapMatrix_genY_eq_transpose_mul_antidiag, Matrix.det_mul, Matrix.det_transpose, Matrix.det_adjugate, Fintype.card_fin,
    show (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0).map C =
      (C : R →+* MvPolynomial (Fin r × Fin r) R).mapMatrix (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0) from rfl,
    ← RingHom.map_det, mul_comm]

private theorem detY_mul_adjugate_subst_adjugate_eq_X {R : Type} [CommRing R] (r : ℕ) (v : Fin r × Fin r) :
    detY R r * aeval (fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) ((genY R r).adjugate v.2.rev v.1) =
      C (Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0).det * detY R r ^ (r - 1) * X v := by
  set P0 : Matrix (Fin r) (Fin r) R := Matrix.of fun k b : Fin r => if k = b.rev then (1 : R) else 0 with hP0
  set G := genY R r with hG
  set Pm : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) R) := (C : R →+* MvPolynomial (Fin r × Fin r) R).mapMatrix P0 with hPm
  have hPP : Pm * Pm = 1 := by
    rw [hPm, ← map_mul, hP0, antidiagonal_mul_self_eq_one, map_one]
  have hdP : Pm.det = C P0.det := by rw [hPm, ← RingHom.map_det]
  have hadjP : Pm.adjugate = Pm.det • Pm := by
    calc Pm.adjugate = Pm.adjugate * (Pm * Pm) := by rw [hPP, Matrix.mul_one]
      _ = Pm.det • Pm := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hAA : G.det • G.adjugate.adjugate = G.det ^ (r - 1) • G := by
    have h1 : G.adjugate * G.adjugate.adjugate = G.det ^ (r - 1) • (1 : Matrix (Fin r) (Fin r) _) := by
      rw [Matrix.mul_adjugate, Matrix.det_adjugate, Fintype.card_fin]
    calc G.det • G.adjugate.adjugate = (G * G.adjugate) * G.adjugate.adjugate := by
          rw [Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
      _ = G * (G.adjugate * G.adjugate.adjugate) := Matrix.mul_assoc _ _ _
      _ = G.det ^ (r - 1) • G := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hY : (aeval fun v : Fin r × Fin r => G.adjugate v.2.rev v.1).mapMatrix G = G.adjugate.transpose * Pm := by
    rw [hG, hPm, adjugate_subst_mapMatrix_genY_eq_transpose_mul_antidiag]; rfl
  have h1 : aeval (fun v : Fin r × Fin r => G.adjugate v.2.rev v.1) (G.adjugate v.2.rev v.1) =
      ((aeval fun v : Fin r × Fin r => G.adjugate v.2.rev v.1).mapMatrix G.adjugate) v.2.rev v.1 := rfl
  have hsel : (Pm * G.adjugate.adjugate.transpose) v.2.rev v.1 = G.adjugate.adjugate v.1 v.2 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single v.2]
    · simp [Pm, P0]
    · intro k _ hk
      have : v.2.rev ≠ k.rev := fun e => hk (Fin.rev_injective e).symm
      simp [Pm, P0, this]
    · simp
  rw [h1, AlgHom.map_adjugate, hY, Matrix.adjugate_mul_distrib, hadjP, ← Matrix.adjugate_transpose, Matrix.smul_mul,
    Matrix.smul_apply, hsel, detY_eq, hdP, smul_eq_mul]
  have h2 := congrFun (congrFun hAA v.1) v.2
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  rw [mul_left_comm, h2]
  simp [G, genY, mul_assoc]

private theorem leftAct_detY_eq_det_mul_detY {R : Type} [CommRing R] (r : ℕ) (A : Matrix (Fin r) (Fin r) R) :
    rowAct R A (detY R r) = C A.det * detY R r := by
  have hAm : (rowAct R A).mapMatrix (genY R r) = (C : R →+* MvPolynomial (Fin r × Fin r) R).mapMatrix A * genY R r := by
    refine Matrix.ext fun a c => ?_
    simp [rowAct, genY, Matrix.mul_apply, aeval_X]
  rw [detY_eq, AlgHom.map_det, hAm, Matrix.det_mul, ← RingHom.map_det]

theorem tauP : TauP := by
  intro O K _ _ _ _ _ hinj r N e α hr hα hαN heα hex
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  haveI : Infinite O := Infinite.of_injective (Nat.cast : ℕ → O) Nat.cast_injective
  obtain ⟨i0, hi0⟩ := hex
  have hD : N - e ≤ ∑ j : Fin r, (N - α j.rev) := by
    have := Finset.single_le_sum (f := fun j : Fin r => N - α j.rev) (fun j _ => Nat.zero_le _) (Finset.mem_univ i0.rev)
    simpa [Fin.rev_rev, hi0] using this
  set D := ∑ j : Fin r, (N - α j.rev) with hDdef
  set Q := D - (N - e) with hQdef
  have hsplit : ∀ (ν : Fin r → ℕ) (a : Fin r), (∑ j, if j = a then 0 else ν j) + ν a = ∑ j, ν j := by
    intro ν a
    have h1 : ∀ j, ν j = (if j = a then 0 else ν j) + (if j = a then ν j else 0) := by
      intro j; split_ifs <;> simp
    calc (∑ j, if j = a then 0 else ν j) + ν a
        = ∑ j, ((if j = a then 0 else ν j) + (if j = a then ν j else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
      _ = ∑ j, ν j := Finset.sum_congr rfl (fun j _ => (h1 j).symm)
  have hψ : (fun k => ∑ j, if j = k.rev then 0 else (fun i : Fin r => N - α i.rev) j) = fun k => (α k - e) + Q := by
    funext k
    have h1 := hsplit (fun i : Fin r => N - α i.rev) k.rev
    simp only [Fin.rev_rev] at h1
    have := hαN k
    have := heα k
    beta_reduce
    omega
  have hanti : Antitone fun i : Fin r => α i - e := fun a b hab => Nat.sub_le_sub_right (hα hab) e
  have keyA : ∀ (R : Type) [CommRing R] [IsDomain R] [Infinite R] (f : MvPolynomial (Fin r × Fin r) R),
      f ∈ dualWeyl R r r (fun i => N - α i.rev) →
      ∃ u ∈ dualWeyl R r r (fun i => α i - e),
        aeval (fun v : Fin r × Fin r => (genY R r).adjugate v.2.rev v.1) f = detY R r ^ Q * u := by
    intro R _ _ _ f hf
    have h7 := dualWeyl_of_eq (adjugate_subst_mem_dualWeyl_of_mem r _ f hf) hψ
    exact detDivP R r Q (fun i => α i - e) hr hanti _ h7
  have hdK : detY K r ^ Q ≠ 0 := pow_ne_zero _ (detY_ne_zero K r)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.mulLeft K (detY K r ^ Q))
    (LinearMap.ker_eq_bot.mpr fun a b h => mul_left_cancel₀ hdK (by simpa using h))
  have hgv : ∀ u, g (detY K r ^ Q * u) = u := by
    intro u
    have := LinearMap.congr_fun hg u
    simpa using this
  have hmap : ∀ f : MvPolynomial (Fin r × Fin r) O,
      (mapAlgHom (Algebra.ofId O K)).toLinearMap f = map (algebraMap O K) f := fun f => rfl
  refine ⟨g ∘ₗ (aeval fun v : Fin r × Fin r => (genY K r).adjugate v.2.rev v.1).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨u, hu, h⟩ := keyA K f hf
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, hgv]
    exact hu
  · intro f hf
    obtain ⟨f0, hf0, rfl⟩ := Submodule.mem_map.mp hf
    obtain ⟨u, hu, h⟩ := keyA O f0 hf0
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hmap, ← map_aeval_adjugate_subst_eq_aeval_map, h, map_mul, map_pow, detY_map, hgv]
    exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
  · intro gg hgg
    obtain ⟨g0, hg0, rfl⟩ := Submodule.mem_map.mp hgg
    set β : Fin r → ℕ := fun i => α i - e with hβ
    set i00 : Fin r := ⟨0, hr⟩ with hi00
    set Dg := ∑ j, β j with hDg
    set Q' := Dg - β i00 with hQ'
    have hβ0 : β i00 ≤ Dg := Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i00)
    have hle : ∀ k : Fin r, i00 ≤ k := fun k => Nat.zero_le _
    have hψ' : (fun k : Fin r => ∑ j, if j = k.rev then 0 else β j) = fun k : Fin r => (β i00 - β k.rev) + Q' := by
      funext k
      have h1 := hsplit β k.rev
      have h2 : β k.rev ≤ β i00 := hanti (hle k.rev)
      omega
    have hγ : Antitone fun k : Fin r => β i00 - β k.rev := by
      intro a b hab
      have : β a.rev ≤ β b.rev := hanti (Fin.rev_le_rev.mpr hab)
      beta_reduce
      omega
    obtain ⟨h0, hh0, hSg⟩ := detDivP O r Q' (fun k => β i00 - β k.rev) hr hγ _
      (dualWeyl_of_eq (adjugate_subst_mem_dualWeyl_of_mem r β g0 hg0) hψ')
    set c := N - α i00 with hc
    set ε : O := (Matrix.of fun k b : Fin r => if k = b.rev then (1 : O) else 0).det with hε
    have hε2 : ε * ε = 1 := by
      rw [hε, ← Matrix.det_mul, antidiagonal_mul_self_eq_one, Matrix.det_one]
    set k := c + Dg + Q' with hk
    set f0 := ε ^ k • (detY O r ^ c * h0) with hf0
    have hf0mem : f0 ∈ dualWeyl O r r (fun i => N - α i.rev) := by
      refine Submodule.smul_mem _ _ ?_
      refine dualWeyl_of_eq (dualWeyl_mul O r r _ _ (dualWeyl_pow (detY_mem_dualWeyl_const_one r) c) hh0) ?_
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, hβ]
      have := hαN i.rev
      have := heα i.rev
      have := hα (hle i.rev)
      have := hαN i00
      omega
    refine ⟨map (algebraMap O K) f0, Submodule.mem_map.mpr ⟨f0, hf0mem, rfl⟩, ?_⟩
    set SO : MvPolynomial (Fin r × Fin r) O →ₐ[O] MvPolynomial (Fin r × Fin r) O :=
      aeval (fun v : Fin r × Fin r => (genY O r).adjugate v.2.rev v.1) with hSO
    set d := detY O r with hd
    set E := C ε * d ^ (r - 1) with hE
    have hdne : d ≠ 0 := by
      intro h0'
      have := congrArg (map (algebraMap O K)) h0'
      rw [hd, detY_map, map_zero] at this
      exact detY_ne_zero K r this
    have hεne : C ε ≠ (0 : MvPolynomial (Fin r × Fin r) O) := by
      intro h'
      have : ε = 0 := C_injective (Fin r × Fin r) O (by rw [h', C_0])
      rw [this, zero_mul] at hε2
      exact zero_ne_one hε2
    have hEne : E ≠ 0 := mul_ne_zero hεne (pow_ne_zero _ hdne)
    have hSd : SO d = E := adjugate_subst_detY_eq_det_antidiag_mul_pow r
    have hSS : SO (SO g0) = aeval (fun v : Fin r × Fin r => SO ((genY O r).adjugate v.2.rev v.1)) g0 := by
      rw [hSO, ← AlgHom.comp_apply, comp_aeval]
    have h10 := pow_mul_aeval_eq_of_homogeneous_of_mul_eq (R := O) (fun v : Fin r × Fin r => SO ((genY O r).adjugate v.2.rev v.1)) X d E
      (fun v => detY_mul_adjugate_subst_adjugate_eq_X (R := O) r v) Dg g0 (degree_eq_sum_of_mem_dualWeyl r r β g0 hg0)
    rw [← hSS, aeval_X_left_apply, hSg, map_mul, map_pow, hSd] at h10
    have hSf0 : SO f0 = C (ε ^ k) * (E ^ c * SO h0) := by
      rw [hf0, map_smul, map_mul, map_pow, hSd, smul_eq_C_mul]
    have hDD : D + Dg = r * (N - e) := by
      have hrev : D = ∑ j : Fin r, (N - α j) := by
        rw [hDdef]
        exact Equiv.sum_comp Fin.revPerm (fun j => N - α j)
      rw [hrev, hDg, ← Finset.sum_add_distrib]
      have : ∀ j, (N - α j) + β j = N - e := by
        intro j
        have := hαN j
        have := heα j
        simp only [hβ]
        omega
      simp [this]
    have hr1 : r * (N - e) = (r - 1) * (N - e) + (N - e) := by
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp [add_mul]
    have hcb : c + β i00 = N - e := by
      have := hαN i00
      have := heα i00
      simp only [hc, hβ]
      omega
    have E1 : (r - 1) * c + (r - 1) * Dg = Dg + (r - 1) * Q' + Q := by
      rw [← mul_add, show c + Dg = (N - e) + Q' by omega, mul_add]
      generalize (r - 1) * (N - e) = P at *
      generalize (r - 1) * Q' = P' at *
      generalize r * (N - e) = T at *
      omega
    have key : C (ε ^ k) * E ^ c * E ^ Dg = d ^ Dg * E ^ Q' * d ^ Q := by
      have hC2 : C ε * C ε = (1 : MvPolynomial (Fin r × Fin r) O) := by rw [← map_mul, hε2, map_one]
      have e1 : (C ε) ^ (k + c + Dg) = (C ε : MvPolynomial (Fin r × Fin r) O) ^ Q' := by
        rw [show k + c + Dg = Q' + 2 * (c + Dg) by omega, pow_add, pow_mul, sq, hC2, one_pow, mul_one]
      calc C (ε ^ k) * E ^ c * E ^ Dg = (C ε) ^ (k + c + Dg) * d ^ ((r - 1) * c + (r - 1) * Dg) := by
            rw [hE, map_pow]; ring
        _ = (C ε) ^ Q' * d ^ (Dg + (r - 1) * Q' + Q) := by rw [e1, E1]
        _ = d ^ Dg * E ^ Q' * d ^ Q := by rw [hE]; ring
    have hcore : SO f0 = d ^ Q * g0 := by
      apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero Dg hdne) (pow_ne_zero Q' hEne))
      calc d ^ Dg * E ^ Q' * SO f0 = C (ε ^ k) * E ^ c * (d ^ Dg * (E ^ Q' * SO h0)) := by rw [hSf0]; ring
        _ = C (ε ^ k) * E ^ c * (E ^ Dg * g0) := by rw [h10]
        _ = (C (ε ^ k) * E ^ c * E ^ Dg) * g0 := by ring
        _ = d ^ Dg * E ^ Q' * d ^ Q * g0 := by rw [key]
        _ = d ^ Dg * E ^ Q' * (d ^ Q * g0) := by ring
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← map_aeval_adjugate_subst_eq_aeval_map,
      show (aeval fun v : Fin r × Fin r => (genY O r).adjugate v.2.rev v.1) f0 = d ^ Q * g0 from hcore,
      map_mul, map_pow, hd, detY_map, hgv]
    all_goals rfl
  · intro l hl f hf
    obtain ⟨u0, hu0, h0⟩ := keyA K f hf
    obtain ⟨u1, hu1, h1⟩ := keyA K (rowAct K l f) (dualWeylRowStable K r r _ l f hf)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [h0, h1, hgv, hgv]
    have hdl : l.det ≠ 0 := hl.ne_zero
    have h12 := congrArg (fun F => F f) (transpose_act_comp_adjugate_subst_comp_act_eq_det r l)
    simp only [AlgHom.comp_apply] at h12
    have h10 := pow_mul_aeval_eq_of_homogeneous_of_mul_eq (R := K) (fun v : Fin r × Fin r => C l.det * (genY K r).adjugate v.2.rev v.1)
      (fun v : Fin r × Fin r => (genY K r).adjugate v.2.rev v.1) 1 (C l.det) (fun v => one_mul _) D f
      (degree_eq_sum_of_mem_dualWeyl r r _ f hf)
    rw [one_pow, one_mul, ← h12, h1, h0, map_mul, map_pow, leftAct_detY_eq_det_mul_detY, Matrix.det_transpose] at h10
    have hDQ : D = Q + (N - e) := by omega
    rw [hDQ, pow_add] at h10
    have hCne : (C l.det : MvPolynomial (Fin r × Fin r) K) ≠ 0 := by
      intro h'; exact hdl (C_injective (Fin r × Fin r) K (by rw [h', C_0]))
    have h11 : (C l.det ^ Q * detY K r ^ Q) * rowAct K l.transpose u1 =
        (C l.det ^ Q * detY K r ^ Q) * (C l.det ^ (N - e) * u0) := by
      linear_combination h10
    have h13 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero Q hCne) hdK) h11
    rw [h13, smul_eq_C_mul, map_pow]

end Formalism.MainNotions.flipOneThree.Pf

end
