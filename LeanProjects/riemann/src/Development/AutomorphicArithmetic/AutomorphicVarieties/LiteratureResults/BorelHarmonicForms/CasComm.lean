import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameBr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem comm_sq {A : Type} [Ring A] (x y z : A) (h : x * y - y * x = z) :
    x * (y * y) - y * y * x = z * y + y * z := by
  rw [← h]; noncomm_ring

theorem UpperTheory.V.Lit.Bor.casComm :
    UpperTheory.V.Lit.Bor.CasComm := by
  intro E _ _ _ a n e he A _ _ _ _ L hL X
  obtain ⟨h1, h2⟩ := frameBr E a n e he A
  let l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] A :=
    { toFun := fun Y => L (toL Y)
      map_add' := fun Y Z => L.map_add (toL Y) (toL Z)
      map_smul' := fun c Y => L.map_smul c (toL Y) }
  have hl : ∀ Y Z, l Y * l Z - l Z * l Y = l (Y * Z - Z * Y) := hL
  let J : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    { toFun := fun Y => Complex.I • Y
      map_add' := fun Y Z => smul_add _ _ _
      map_smul' := fun c Y => smul_comm _ _ _ }
  let s : Herm E a →ₗ[ℝ] A := l ∘ₗ (Herm E a).subtype
  let t : Herm E a →ₗ[ℝ] A := l ∘ₗ J ∘ₗ (Herm E a).subtype
  have key : ∀ Y, l Y * cas L e - cas L e * l Y =
      ∑ j, (l (Y * (e j).1 - (e j).1 * Y) * l (e j).1 + l (e j).1 * l (Y * (e j).1 - (e j).1 * Y)) -
      ∑ j, (l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y) * l (Complex.I • (e j).1) +
        l (Complex.I • (e j).1) * l (Y * (Complex.I • (e j).1) - (Complex.I • (e j).1) * Y)) := fun Y => by
    have hc : cas L e = ∑ j, (l (e j).1 * l (e j).1 - l (Complex.I • (e j).1) * l (Complex.I • (e j).1)) := rfl
    rw [hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← comm_sq _ _ _ (hl Y _), ← comm_sq _ _ _ (hl Y _)]
    noncomm_ring
  have hskew : ∀ Z, star Z = -Z → l Z * cas L e - cas L e * l Z = 0 := fun Z hZ => by
    have a1 : ∑ j, l (Z * (e j).1 - (e j).1 * Z) * l (e j).1 + ∑ j, l (e j).1 * l (Z * (e j).1 - (e j).1 * Z) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ s s) Z hZ
    have a2 : ∑ j, l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) * l (Complex.I • (e j).1) +
        ∑ j, l (Complex.I • (e j).1) * l (Complex.I • (Z * (e j).1 - (e j).1 * Z)) = 0 :=
      h1 ((LinearMap.mul ℝ A).compl₁₂ t t) Z hZ
    rw [key]
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, Finset.sum_add_distrib]
    rw [a1, a2, sub_zero]
  have hherm : ∀ Y : Herm E a, l Y.1 * cas L e - cas L e * l Y.1 = 0 := fun Y => by
    have hs : ∀ j, star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := fun j => by
      have h : star (e j).1 = (e j).1 := (e j).2
      rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
    have a1 : ∑ j, (l (Y.1 * (e j).1 - (e j).1 * Y.1) * l (e j).1 + l (e j).1 * l (Y.1 * (e j).1 - (e j).1 * Y.1)) =
        -∑ j, (l (Complex.I • (e j).1) * l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) +
          l ((Complex.I • (e j).1) * Y.1 - Y.1 * (Complex.I • (e j).1)) * l (Complex.I • (e j).1)) :=
      h2 ((LinearMap.mul ℝ A).compl₁₂ l s + (LinearMap.mul ℝ A).flip.compl₁₂ l s) Y hs
    rw [key, a1, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← neg_sub (Y.1 * (Complex.I • (e j).1)), map_neg]
    noncomm_ring
  let Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X
  have hY : Y = (hp (toL Y)).1 + (1 / 2 : ℝ) • (Y - star Y) := by
    rw [hp_val]; module
  have hZ : star ((1 / 2 : ℝ) • (Y - star Y)) = -((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [star_smul, star_trivial, star_sub, star_star, ← smul_neg, neg_sub]
  have hX : L X = l (hp (toL Y)).1 + l ((1 / 2 : ℝ) • (Y - star Y)) := by
    rw [← map_add, ← hY]; rfl
  rw [hX]
  exact Commute.add_right (Commute.symm (sub_eq_zero.1 (hherm _))) (Commute.symm (sub_eq_zero.1 (hskew _ hZ)))
