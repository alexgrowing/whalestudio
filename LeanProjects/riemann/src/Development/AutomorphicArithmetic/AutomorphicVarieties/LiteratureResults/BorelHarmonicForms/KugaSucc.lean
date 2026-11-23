import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameBr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ring_sq {R : Type} [Ring R] {x y : R} (h : Commute x y) : (y - x) * (x + y) = y * y - x * x := by
  have h' := h.eq
  rw [sub_mul, mul_add, mul_add, h']
  abel

private theorem ring_br {R : Type} [Ring R] {x y x' y' : R} (h : Commute x y') (h' : Commute x' y) :
    (x + y) * (y' - x') - (y' - x') * (x + y) = (y * y' - y' * y) - (x * x' - x' * x) := by
  simp only [sub_mul, mul_add, add_mul, mul_sub, h.eq, h'.eq]
  abel

theorem UpperTheory.V.Lit.Bor.kugaSucc :
    UpperTheory.V.Lit.Bor.KugaSucc := by
  intro E _ _ _ a n e he M _ _ _ _ A B hA hB hAB q ω hω X
  have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have hsq : ∀ (Z : Lie E a) (m : M), (B - A) Z ((A + B) Z m) = (B Z * B Z - A Z * A Z) m := fun Z m =>
    LinearMap.congr_fun (ring_sq (hAB Z Z)) m
  have hbr : ∀ (Y Z : Matrix (Fin a) (Fin a) (Cinf E)) (m : M),
      (A + B) (toL Y) ((B - A) (toL Z) m) - (B - A) (toL Z) ((A + B) (toL Y) m) =
        (B - A) (toL (Y * Z - Z * Y)) m := fun Y Z m => by
    have h := ring_br (hAB (toL Y) (toL Z)) (hAB (toL Z) (toL Y))
    rw [hA, hB] at h
    exact LinearMap.congr_fun h m
  have hup : ∀ (i : Fin (q + 1)) (Y : Herm E a),
      (-1 : ℤ) ^ (i : ℕ) • ω (Matrix.vecCons Y (i.removeNth X)) = ω (Function.update X i Y) := fun i Y => by
    rw [← Fin.insertNth_removeNth, AlternatingMap.map_insertNth]
  have hfr : ∀ i : Fin (q + 1),
      ∑ j, (B - A) (toL ((X i).1 * (e j).1 - (e j).1 * (X i).1)) (ω (Function.update X i (e j))) =
        -∑ j, (B - A) (toL (Complex.I • (e j).1)) (ω (Function.update X i (brH _ (hs j) (X i)))) := fun i =>
    (frameBr E a n e he M).2
      (LinearMap.mk₂ ℝ (fun Z Y => (B - A) (toL Z) (ω (Function.update X i Y)))
        (fun Z Z' Y => LinearMap.congr_fun (map_add (B - A) (toL Z) (toL Z')) _)
        (fun c Z Y => LinearMap.congr_fun (map_smul (B - A) c (toL Z)) _)
        (fun Z Y Y' => by rw [AlternatingMap.map_update_add, map_add])
        (fun c Z Y => by rw [AlternatingMap.map_update_smul, LinearMap.map_smul_of_tower])) (X i) hs
  have h1 : dCo (A + B) (del (B - A) e ω) X =
      ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) := by
    rw [dCo_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hup, map_zsmul, map_zsmul]
  have h2 : del (B - A) e (dCo (A + B) ω) X =
      ∑ j, ((B - A) (toL (e j).1) ((A + B) (toL (e j).1) (ω X)) -
        ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j))))) := by
    rw [del_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dCo_cons, map_sub, dCo_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hup, map_zsmul, map_zsmul, map_zsmul]
    rfl
  have h3 : ∑ j, ∑ i, (A + B) (toL (X i).1) ((B - A) (toL (e j).1) (ω (Function.update X i (e j)))) -
      ∑ j, ∑ i, (B - A) (toL (e j).1) ((A + B) (toL (X i).1) (ω (Function.update X i (e j)))) =
      -∑ j, (B - A) (toL (Complex.I • (e j).1)) ((A + B) (toL (Complex.I • (e j).1)) (ω X)) := by
    simp only [← Finset.sum_sub_distrib, hbr]
    rw [Finset.sum_comm]
    simp only [hfr]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω _ (hs j), map_sum]
  rw [h1, h2, Finset.sum_sub_distrib, add_sub_left_comm, h3, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    cas, cas, ← Finset.sum_sub_distrib, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsq, hsq]
  simp only [LinearMap.sub_apply]
  abel
