import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgMulSelf
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.ClifP

variable {n : ℕ}

private abbrev Io (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2}

private abbrev Mt (n : ℕ) : Type := Matrix (Finset (Io n)) (Finset (Io n)) ℂ

private def rr : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

private lemma rr_sq : rr * rr = 1 / 2 := by
  unfold rr
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private lemma rr_conj : star rr = rr := by
  unfold rr
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

private def pr (a b : Fin n) : Io n := ⟨(min a b, max a b), min_le_max⟩

private lemma pr_comm (a b : Fin n) : pr a b = pr b a := by
  unfold pr
  simp only [min_comm a b, max_comm a b]

private def cs (a b : Fin n) : ℂ := if a < b then 0 else if b < a then 1 else rr

private lemma cs_conj (a b : Fin n) : star (cs a b) = cs a b := by
  unfold cs; split_ifs <;> simp [rr_conj]

private lemma cs_lt {a b : Fin n} (h : a < b) : cs a b = 0 := by simp [cs, h]
private lemma cs_gt {a b : Fin n} (h : b < a) : cs a b = 1 := by
  simp [cs, h, not_lt.mpr h.le]

private def cM (α : Io n → Mt n) (a b : Fin n) : Mt n :=
  cs a b • α (pr a b) + cs b a • (α (pr a b))ᴴ

private lemma anti {R : Type} [Ring R] [Algebra ℂ R] (u u' v v' e : R) (s t s' t' : ℂ)
    (h1 : u * u' + u' * u = 0) (h2 : u * v' + v' * u = e) (h3 : v * u' + u' * v = e)
    (h4 : v * v' + v' * v = 0) :
    (s • u + t • v) * (s' • u' + t' • v') + (s' • u' + t' • v') * (s • u + t • v)
      = (s * t' + t * s') • e := by
  calc (s • u + t • v) * (s' • u' + t' • v') + (s' • u' + t' • v') * (s • u + t • v)
      = (s * s') • (u * u' + u' * u) + (s * t') • (u * v' + v' * u)
        + (t * s') • (v * u' + u' * v) + (t * t') • (v * v' + v' * v) := by
        simp only [add_mul, mul_add, smul_mul_smul_comm, smul_add, mul_comm s' s, mul_comm t' t,
          mul_comm s' t, mul_comm t' s]
        abel
    _ = (s * t' + t * s') • e := by
        rw [h1, h2, h3, h4, smul_zero, smul_zero, zero_add, add_zero, add_smul]

private lemma comb1 (a b d e : Fin n) (h : pr a b = pr d e) :
    cs a b * cs e d + cs b a * cs d e = if b = d ∧ a = e then 1 else 0 := by
  simp only [pr, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [min_def, min_def] at h1
  rw [max_def, max_def] at h2
  unfold cs
  split_ifs at h1 h2 <;> split_ifs <;> first | omega | (simp_all [rr_sq]; done) | (simp_all [rr_sq]; norm_num)

private lemma relC (α : Io n → Mt n) (h1 : ∀ i j, α i * α j + α j * α i = 0)
    (h2 : ∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) : Clif (cM α) := by
  intro a b d e
  have k2 : α (pr a b) * (α (pr d e))ᴴ + (α (pr d e))ᴴ * α (pr a b)
      = if pr a b = pr d e then 1 else 0 := h2 _ _
  have k3 : (α (pr a b))ᴴ * α (pr d e) + α (pr d e) * (α (pr a b))ᴴ
      = if pr a b = pr d e then 1 else 0 := by
    rw [add_comm, h2]
    simp only [eq_comm]
  have k4 : (α (pr a b))ᴴ * (α (pr d e))ᴴ + (α (pr d e))ᴴ * (α (pr a b))ᴴ = 0 := by
    have := congrArg Matrix.conjTranspose (h1 (pr d e) (pr a b))
    simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul] using this
  unfold cM
  rw [anti _ _ _ _ _ _ _ _ _ (h1 _ _) k2 k3 k4]
  by_cases hp : pr a b = pr d e
  · rw [comb1 a b d e hp, if_pos hp]
    split_ifs <;> simp
  · rw [if_neg hp, smul_zero, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hp (pr_comm _ _)

private lemma adjC (α : Io n → Mt n) (a b : Fin n) : (cM α a b)ᴴ = cM α b a := by
  unfold cM
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, cs_conj, cs_conj, pr_comm b a, add_comm]

private def sg (a d : Fin n) : ℝ := (if a < d then 1 else 0) - (if d < a then 1 else 0)

private def eta (A : Finset (Io n)) : Wt n := -rhoV n + ∑ i ∈ A, rt i.1.1 i.1.2

private lemma sg_sum (a : Fin n) : ∑ d, sg a d = 2 * rhoV n a := by
  simp only [sg, Finset.sum_sub_distrib, Finset.sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  simp only [rhoV]
  have := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private lemma rt_eq (i : Io n) (a : Fin n) :
    rt i.1.1 i.1.2 a = ∑ d, if pr a d = i then sg a d else 0 := by
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  dsimp only at hpq
  simp only [pr, Subtype.mk.injEq, Prod.mk.injEq, rt, Pi.sub_apply, Pi.single_apply]
  rw [Finset.sum_eq_single_of_mem (if a = p then q else p) (Finset.mem_univ _)]
  · simp only [sg, min_def, max_def]
    split_ifs <;> first | omega | norm_num
  · intro d _ hd
    simp only [sg, min_def, max_def]
    split_ifs at hd <;> split_ifs <;> first | rfl | omega | norm_num

private lemma sgN (A : Finset (Io n)) (a : Fin n) :
    ∑ d, sg a d * (if pr a d ∈ A then 1 else 0) = ∑ i ∈ A, rt i.1.1 i.1.2 a := by
  simp_rw [rt_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_ite_eq]
  split_ifs <;> simp

private lemma Dlt (α : Io n → Mt n)
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0)
    {a d : Fin n} (h : a < d) :
    cM α a d * cM α d a = Matrix.diagonal fun A => if pr a d ∈ A then 1 else 0 := by
  unfold cM
  rw [cs_lt h, cs_gt h, pr_comm d a]
  simp only [zero_smul, one_smul, zero_add, add_zero]
  exact h3 _

private lemma Dall (α : Io n → Mt n) (hc : Clif (cM α))
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0)
    (a d : Fin n) :
    cM α a d * cM α d a = Matrix.diagonal fun A =>
      1 / 2 + (sg a d : ℂ) * ((if pr a d ∈ A then 1 else 0) - 1 / 2) := by
  rcases lt_trichotomy a d with h | h | h
  · rw [Dlt α h3 h]
    congr 1
    funext A
    simp [sg, h, not_lt.mpr h.le]
  · subst h
    have hcl := hc a a a a
    simp only [and_self, if_true] at hcl
    have hX : cM α a a * cM α a a = (1 / 2 : ℂ) • (1 : Mt n) := by
      have h2 : (2 : ℂ) • (cM α a a * cM α a a) = 1 := by
        rw [two_smul]
        exact hcl
      calc cM α a a * cM α a a = (1 / 2 : ℂ) • ((2 : ℂ) • (cM α a a * cM α a a)) := by
            rw [smul_smul]
            norm_num
        _ = _ := by rw [h2]
    rw [hX]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, sg]
  · have hcl := hc a d d a
    simp only [and_self, if_true] at hcl
    have e := Dlt α h3 h
    have hs : cM α a d * cM α d a = 1 - cM α d a * cM α a d := eq_sub_of_add_eq hcl
    rw [hs, e, pr_comm d a]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, sg, h, not_lt.mpr h.le]
    split_ifs <;> norm_num

private lemma diagC (α : Io n → Mt n) (hc : Clif (cM α))
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0) (a : Fin n) :
    spn (cM α) a a = Matrix.diagonal fun A => ((eta A a : ℝ) : ℂ) := by
  have key : ∀ A : Finset (Io n), (∑ d, ((1 / 2 : ℂ) + (sg a d : ℂ) * ((if pr a d ∈ A then 1 else 0) - 1 / 2)))
      - (n : ℂ) / 2 = ((eta A a : ℝ) : ℂ) := by
    intro A
    have c1 : ∑ d, (sg a d : ℂ) = 2 * (rhoV n a : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (sg_sum a)
      push_cast at this
      exact this
    have c2 : ∑ d, (sg a d : ℂ) * (if pr a d ∈ A then 1 else 0)
        = ((∑ i ∈ A, rt i.1.1 i.1.2 a : ℝ) : ℂ) := by
      rw [← sgN A a]
      push_cast
      refine Finset.sum_congr rfl (fun d _ => ?_)
      split_ifs <;> simp
    have e : eta A a = -rhoV n a + ∑ i ∈ A, rt i.1.1 i.1.2 a := by
      simp [eta, Finset.sum_apply]
    rw [e]
    push_cast
    push_cast at c2
    simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c1, c2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold spn
  simp only [if_true]
  simp_rw [Dall α hc h3 a]
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.algebraMap_matrix_apply]
  split_ifs with hij
  · subst hij
    exact key i
  · simp

private lemma ex_sum {κ : Type} (s : Finset κ) (f : κ → Wt n) :
    ex (∑ i ∈ s, f i) = ∏ i ∈ s, ex (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cfBasic n).2.1
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, (cfBasic n).1, ih]

private lemma chrC : ∑ A : Finset (Io n), ex (eta A) = (2 : ℂ) ^ n • chR n := by
  obtain ⟨hadd, h0, -⟩ := cfBasic n
  obtain ⟨-, -, -, -, -, -, -, hw, hwB⟩ := chRF n
  have s1 : ∀ A : Finset (Io n), ex (eta A) = ex (-rhoV n) * ∏ i ∈ A, ex (rt i.1.1 i.1.2) := by
    intro A
    rw [eta, hadd, ex_sum]
  simp_rw [s1]
  rw [← Finset.mul_sum, ← Finset.powerset_univ, ← Finset.prod_one_add,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Io n => i.1.1 = i.1.2)]
  have hcard' : (Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2)).card
      = (Finset.univ : Finset (Fin n)).card := by
    refine Finset.card_nbij' (fun i => i.1.1) (fun a => ⟨(a, a), le_refl a⟩) ?_ ?_ ?_ ?_
    · intro i _
      simp
    · intro a _
      simp
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      apply Subtype.ext
      ext <;> simp [h]
    · intro a _
      rfl
  have hcard : (Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2)).card = n := by
    rw [hcard', Finset.card_univ, Fintype.card_fin]
  have d1 : ∏ i ∈ Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2), (1 + ex (rt i.1.1 i.1.2))
      = (2:ℂ) ^ n • (1 : FR n) := by
    rw [Finset.prod_congr rfl (g := fun _ => (1 : FR n) + 1)]
    · rw [Finset.prod_const, hcard, ← two_mul, mul_one]
      rw [show (2 : FR n) = (2:ℂ) • (1 : FR n) by rw [two_smul, one_add_one_eq_two]]
      rw [smul_pow, one_pow]
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      rw [h]
      simp [rt, h0]
  have d2 : ∏ i ∈ Finset.univ.filter (fun i : Io n => ¬ i.1.1 = i.1.2), (1 + ex (rt i.1.1 i.1.2))
      = ∏ p ∈ posP n, (1 + ex (rt p.1 p.2)) := by
    refine Finset.prod_nbij' (fun i => i.1) (fun p => pr p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne i.2 h
    · intro p hp
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [pr, min_eq_left hp.le, max_eq_right hp.le, hp.ne]
    · intro i hi
      apply Subtype.ext
      simp [pr, min_eq_left i.2, max_eq_right i.2]
    · intro p hp
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [pr, min_eq_left hp.le, max_eq_right hp.le]
    · intro i _
      rfl
  rw [d1, d2]
  have d3 : ∏ p ∈ posP n, (1 + ex (rt p.1 p.2))
      = ex (wtB (posP n)) * ∏ p ∈ posP n, (1 + ex (-rt p.1 p.2)) := by
    rw [hwB, ex_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [mul_add, mul_one, ← hadd, add_neg_cancel, h0, add_comm]
  rw [d3, hw]
  unfold chR
  rw [smul_mul_assoc, one_mul, mul_smul_comm, ← mul_assoc, ← hadd]
  congr 3
  rw [two_smul]
  abel

end UpperTheory.RealTr.ClifP

theorem UpperTheory.RealTr.clifEx :
    ∀ n : ℕ, ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η := by
  intro n
  obtain ⟨α, h1, h2, h3⟩ := carEx (ClifP.Io n)
  exact ⟨Finset (ClifP.Io n), inferInstance, inferInstance, ClifP.cM α, ClifP.eta,
    ⟨ClifP.relC α h1 h2, ClifP.adjC α, ClifP.diagC α (ClifP.relC α h1 h2) h3, ClifP.chrC⟩⟩
