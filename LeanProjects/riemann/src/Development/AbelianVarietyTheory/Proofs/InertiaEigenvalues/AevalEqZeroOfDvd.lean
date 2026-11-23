import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatMapTmul
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.LagIdem

variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]

noncomputable def lagPoly (a : ι → R) (i : ι) : R[X] :=
  C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) *
    ∏ j ∈ Finset.univ.erase i, (X - C (a j))

end GlobalTheory.LagIdem

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_eq_zero_of_dvd_of_aeval_eq_zero {M : E} {p q : R[X]} (hp : aeval M p = 0) (h : p ∣ q) :
    aeval M q = 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [hp]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
private lemma prod_X_sub_C_dvd_sum_lagPoly_sub_one :
    ∏ j, (X - C (a j)) ∣ ∑ i, _root_.GlobalTheory.LagIdem.lagPoly a i - 1 := by
  refine Fintype.prod_dvd_of_coprime
    (fun i j hij => isCoprime_X_sub_C_of_isUnit_sub (hu i j hij)) fun k => ?_
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_one, eval_finset_sum, sub_eq_zero,
    Finset.sum_eq_single k]
  · simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact Ring.inverse_mul_cancel _
      (IsUnit.prod_iff.mpr fun j hj => hu k j (Finset.ne_of_mem_erase hj).symm)
  · intro i _ hik
    simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩) (sub_self _))
  · intro h
    exact absurd (Finset.mem_univ k) h

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_lagPoly_eq_lagIdem (M : E) (a : ι → R) (i : ι) :
    aeval M (_root_.GlobalTheory.LagIdem.lagPoly a i) = _root_.GlobalTheory.Pat.lagIdem M a i := by
  simp [_root_.GlobalTheory.LagIdem.lagPoly, _root_.GlobalTheory.Pat.lagIdem, Algebra.smul_def]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma prod_X_sub_C_eq_mul_prod_erase (a : ι → R) (i : ι) :
    ∏ j, (X - C (a j)) = (X - C (a i)) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
omit hu in
private lemma prod_X_sub_C_dvd_lagPoly_mul_of_ne {i j : ι} (hij : i ≠ j) :
    ∏ l, (X - C (a l)) ∣ _root_.GlobalTheory.LagIdem.lagPoly a i * _root_.GlobalTheory.LagIdem.lagPoly a j := by
  rw [prod_X_sub_C_eq_mul_prod_erase a i]
  have h : X - C (a i) ∣ ∏ l ∈ Finset.univ.erase j, (X - C (a l)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  obtain ⟨q, hq⟩ := h
  refine ⟨C (Ring.inverse (∏ l ∈ Finset.univ.erase i, (a i - a l))) *
    C (Ring.inverse (∏ l ∈ Finset.univ.erase j, (a j - a l))) * q, ?_⟩
  simp only [_root_.GlobalTheory.LagIdem.lagPoly, hq]
  ring

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma commute_aeval_of_commute' {T M : E} (h : Commute T M) (p : R[X]) :
    Commute T (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact Commute.mul_right (show Commute T (algebraMap R E c) from (Algebra.commutes c T).symm)
      (h.pow_right n)

open TensorProduct Polynomial IsLocalRing in
theorem _root_.GlobalTheory.lagIdem_spec : ∀ (R E ι : Type) [CommRing R]
    [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : E) (a : ι → R),
    (∀ i j, i ≠ j → IsUnit (a i - a j)) → Polynomial.aeval M (∏ j, (X - C (a j))) = 0 →
    CompleteOrthogonalIdempotents (_root_.GlobalTheory.Pat.lagIdem M a) ∧
      (∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i = a i • _root_.GlobalTheory.Pat.lagIdem M a i) ∧
      M = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i ∧
      ∀ (T : E) i, Commute T M → Commute T (_root_.GlobalTheory.Pat.lagIdem M a i) := by
  intro R E ι _ _ _ _ _ _ M a hu hM
  have hsum : ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i = 1 := by
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_sum_lagPoly_sub_one a hu)
    simpa [map_sum, aeval_lagPoly_eq_lagIdem, sub_eq_zero] using h
  have hortho : ∀ i j, i ≠ j →
      _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a j = 0 := by
    intro i j hij
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_lagPoly_mul_of_ne a hij)
    simpa [aeval_lagPoly_eq_lagIdem] using h
  have hidem : ∀ i, IsIdempotentElem (_root_.GlobalTheory.Pat.lagIdem M a i) := by
    intro i
    have h : _root_.GlobalTheory.Pat.lagIdem M a i * ∑ j, _root_.GlobalTheory.Pat.lagIdem M a j =
        _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a i := by
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hji => hortho i j (Ne.symm hji))
        (fun h => absurd (Finset.mem_univ i) h)]
    rw [hsum, mul_one] at h
    exact h.symm
  have heigen : ∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i =
      a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
    intro i
    have hdvd : ∏ j, (X - C (a j)) ∣ (X - C (a i)) * _root_.GlobalTheory.LagIdem.lagPoly a i := by
      refine ⟨C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))), ?_⟩
      rw [prod_X_sub_C_eq_mul_prod_erase a i, _root_.GlobalTheory.LagIdem.lagPoly]
      ring
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM hdvd
    rw [map_mul, aeval_lagPoly_eq_lagIdem, map_sub, aeval_X, aeval_C, sub_mul,
      sub_eq_zero, ← Algebra.smul_def] at h
    exact h
  refine ⟨⟨⟨hidem, fun i j hij => hortho i j hij⟩, hsum⟩, heigen, ?_, ?_⟩
  · calc M = M * ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i := by rw [hsum, mul_one]
      _ = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => heigen i
  · intro T i hT
    rw [← aeval_lagPoly_eq_lagIdem]
    exact commute_aeval_of_commute' hT _
