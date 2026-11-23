import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRMulNe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

noncomputable abbrev nagata (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

omit [IsDomain A] in
theorem nagata_comp_neg (c : A) : (nagata f c).comp (nagata f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

noncomputable abbrev nagataEquiv := AlgEquiv.ofAlgHom (nagata f 1) (nagata f (-1))
  (nagata_comp_neg f 1) (by simpa using nagata_comp_neg f (-1))

omit [IsDomain A] in
variable {f v} in
theorem lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

theorem sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x :=
  by apply _root_.UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne <;> assumption

theorem degreeOf_zero_nagata {a : A} (ha : a ≠ 0) : ((nagataEquiv f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := A) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

theorem degreeOf_nagata_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (nagataEquiv f <| monomial v <| coeff v f).degreeOf 0 ≠
    (nagataEquiv f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_nagata _ _ <| mem_support_iff.mp hv,
    degreeOf_zero_nagata _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

theorem leadingCoeff_finSuccEquiv_nagata :
    (finSuccEquiv A n ((nagataEquiv f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap A _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv A n) ((nagata f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

theorem exists_leadingCoeff_nagata (fne : f ≠ 0) :
    ∃ c : A, c ≠ 0 ∧ (finSuccEquiv A n (nagataEquiv f f)).leadingCoeff = MvPolynomial.C c := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (nagataEquiv f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  refine ⟨coeff v f, mem_support_iff.mp vin, ?_⟩
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv A n ((nagataEquiv f) (h x))).degree <
      (finSuccEquiv A n ((nagataEquiv f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_nagata_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv A n ((nagataEquiv f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv A n ((nagataEquiv f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv A n ((nagataEquiv f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_nagata] at coeff
  simpa only [algebraMap_eq] using coeff

end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

def CombAfterPower (c : A) (z : Fin m → D) (s : Finset D) (d : D) : Prop :=
  ∃ (k : ℕ) (cf : D → MvPolynomial (Fin m) A), c ^ k • d = ∑ t ∈ s, aeval z (cf t) * t

variable {c : A} {z : Fin m → D} {s : Finset D}

theorem smul_sum_aeval (b : A) (cf : D → MvPolynomial (Fin m) A) :
    b • ∑ t ∈ s, aeval z (cf t) * t = ∑ t ∈ s, aeval z (MvPolynomial.C b * cf t) * t := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, MvPolynomial.aeval_C, Algebra.smul_def, mul_assoc]

theorem CombAfterPower.zero : CombAfterPower c z s 0 :=
  ⟨0, fun _ ↦ 0, by simp⟩

theorem CombAfterPower.add {d e : D} (hd : CombAfterPower c z s d) (he : CombAfterPower c z s e) :
    CombAfterPower c z s (d + e) := by
  obtain ⟨k, f, hf⟩ := hd
  obtain ⟨l, g, hg⟩ := he
  refine ⟨k + l, fun t ↦ MvPolynomial.C (c ^ l) * f t + MvPolynomial.C (c ^ k) * g t, ?_⟩
  have h1 : c ^ (k + l) • d = c ^ l • (c ^ k • d) := by rw [smul_smul, ← pow_add, add_comm]
  have h2 : c ^ (k + l) • e = c ^ k • (c ^ l • e) := by rw [smul_smul, ← pow_add]
  rw [smul_add, h1, h2, hf, hg, smul_sum_aeval, smul_sum_aeval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_add, add_mul]

theorem CombAfterPower.mul_left (P : MvPolynomial (Fin m) A) {d : D} (hd : CombAfterPower c z s d) :
    CombAfterPower c z s (aeval z P * d) := by
  obtain ⟨k, f, hf⟩ := hd
  refine ⟨k, fun t ↦ P * f t, ?_⟩
  rw [← mul_smul_comm, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, mul_assoc]

theorem CombAfterPower.sum {ι : Type*} (u : Finset ι) (F : ι → D)
    (h : ∀ i ∈ u, CombAfterPower c z s (F i)) : CombAfterPower c z s (∑ i ∈ u, F i) :=
  Finset.sum_induction _ _ (fun _ _ ↦ CombAfterPower.add) CombAfterPower.zero h

theorem CombAfterPower.of_smul {d : D} (h : CombAfterPower c z s (c • d)) :
    CombAfterPower c z s d := by
  obtain ⟨k, f, hf⟩ := h
  exact ⟨k + 1, f, by rw [pow_succ, mul_smul, hf]⟩

theorem CombAfterPower.of_mem {t : D} (ht : t ∈ s) : CombAfterPower c z s t := by
  classical
  refine ⟨0, fun u ↦ if u = t then 1 else 0, ?_⟩
  rw [pow_zero, one_smul, Finset.sum_eq_single t (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd ht h)]
  simp

theorem combAfterPower_pow [DecidableEq D] (w : D) (N : ℕ) (b : ℕ → MvPolynomial (Fin m) A)
    (hrel : c • w ^ N = ∑ i ∈ Finset.range N, aeval z (b i) * w ^ i) (j : ℕ) :
    CombAfterPower c z ((Finset.range N).image (fun i ↦ w ^ i)) (w ^ j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  by_cases hj : j < N
  · exact CombAfterPower.of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hj))
  · replace hj := not_lt.mp hj
    apply CombAfterPower.of_smul
    have e : c • w ^ j = ∑ i ∈ Finset.range N, aeval z (b i) * w ^ (i + (j - N)) := by
      have : w ^ j = w ^ (j - N) * w ^ N := by rw [← pow_add, Nat.sub_add_cancel hj]
      rw [this, ← mul_smul_comm, hrel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pow_add]
      ring
    rw [e]
    exact CombAfterPower.sum _ _ fun i hi ↦ CombAfterPower.mul_left _
      (ih _ (by have := Finset.mem_range.1 hi; omega))

end Combination

theorem algHom_eq_eval₂_finSuccEquiv {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {n : ℕ}
    (ψ : MvPolynomial (Fin (n + 1)) A →ₐ[A] D) (P : MvPolynomial (Fin (n + 1)) A) :
    ψ P = (finSuccEquiv A n P).eval₂
      (MvPolynomial.aeval (R := A) (fun i : Fin n ↦ ψ (X i.succ))).toRingHom (ψ (X 0)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add P Q hP hQ => rw [map_add, map_add, Polynomial.eval₂_add, hP, hQ]
  | mul_X P i ih =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, ih]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
