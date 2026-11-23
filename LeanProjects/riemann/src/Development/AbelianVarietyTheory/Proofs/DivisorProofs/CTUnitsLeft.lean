import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses

def gramOn {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) :
    Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
  Matrix.of fun i j => hform σ H (Module.finBasis K V i).1 (Module.finBasis K V j).1

def sgnOn {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) : ℂ :=
  (-1) ^ ordL (gramOn σ H (LinearMap.ker (Matrix.toLin' (aeval A Q)))).det

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Gen
variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) K) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_units (k : GL (Fin n) K) : cT σ (k⁻¹).val * cT σ k.val = 1 := by
  rw [← cT_mul, Units.mul_inv, cT_one]

theorem cT_units' (k : GL (Fin n) K) : cT σ k.val * cT σ (k⁻¹).val = 1 := by
  rw [← cT_mul, Units.inv_mul, cT_one]

theorem cT_units_left (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ (k⁻¹).val * (cT σ k.val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units, Matrix.one_mul]

theorem cT_units_left' (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units', Matrix.one_mul]

theorem herm_of (hσ : ∀ x, σ (σ x) = x) (k : GL (Fin n) K) : IsHerm σ (cT σ (k⁻¹).val * (k⁻¹).val) := by
  unfold IsHerm; rw [cT_mul, cT_cT σ hσ]

theorem det_ne (k : GL (Fin n) K) : (cT σ (k⁻¹).val * (k⁻¹).val).det ≠ 0 := by
  have h1 : ((k⁻¹).val).det ≠ 0 := ((k⁻¹).isUnit.map Matrix.detMonoidHom).ne_zero
  have h2 : (cT σ (k⁻¹).val).det = σ ((k⁻¹).val).det := by
    unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [Matrix.det_mul, h2]
  exact mul_ne_zero ((map_ne_zero σ).2 h1) h1

theorem one_of (k : GL (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * (k⁻¹).val) * k.val = 1 := by
  simp only [Matrix.mul_assoc, cT_units_left', Units.inv_mul]

theorem inv_of_unit (k a : GL (Fin n) K) (hy : cT σ (k⁻¹ * a * k).val * 1 * (k⁻¹ * a * k).val = 1) :
    cT σ a.val * (cT σ (k⁻¹).val * (k⁻¹).val) * a.val = cT σ (k⁻¹).val * (k⁻¹).val := by
  have ha : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
  rw [ha]
  generalize k⁻¹ * a * k = y at hy ⊢
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one] at hy ⊢
  simp only [cT_units_left', Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (cT σ y.val), hy, Matrix.one_mul]

theorem unit_of_form (γ₀ h : GL (Fin n) K) (hinv : cT σ γ₀.val * (cT σ h.val * h.val) * γ₀.val = cT σ h.val * h.val) :
    cT σ (h * γ₀ * h⁻¹).val * 1 * (h * γ₀ * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) hinv
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

theorem unit_of_two (k c h : GL (Fin n) K) (H' : Matrix (Fin n) (Fin n) K)
    (h1 : H' = cT σ c.val * (cT σ (k⁻¹).val * (k⁻¹).val) * c.val) (h2 : H' = cT σ h.val * h.val) :
    cT σ (k⁻¹ * c * h⁻¹).val * 1 * (k⁻¹ * c * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) (h1.symm.trans h2)
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

end Gen

theorem cT_map (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (w.adicCompletion E)) =
      cT (cj w) (M.map (algebraMap E (w.adicCompletion E))) := by
  have h := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hw).1
  ext i j; simp [cT, h]

theorem locPt_val (hU : Unr E) {n : ℕ} (w : Pl E) (γ : UE E n) :
    ((locPt w γ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
    unfold UL
    split_ifs with hs
    · trivial
    · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 * γ.1 = 1 := γ.2
      show cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val *
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = 1
      have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hγ
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hs] at this
      simpa using this
  unfold locPt toSub
  rw [dif_pos hm]

theorem aeval_map_mat {n : ℕ} (w : Pl E) (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E (w.adicCompletion E))) (atPl w p) = (aeval M p).map (algebraMap E (w.adicCompletion E)) := by
  rw [atPl, aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E (w.adicCompletion E))) M p
  have e : (⇑(Algebra.ofId E (w.adicCompletion E)) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem kapSign_eq {n : ℕ} (w : Pl E) (hw : ¬ IsSplitAt w) (Q : (w.adicCompletion E)[X]) (γ : GLw n w) :
    kapSign n w Q γ = sgnOn (cj w) 1 Q γ.val := by
  unfold kapSign sgnOn gramOn hform
  rw [if_neg hw]
  simp [Matrix.one_apply]

theorem mem_S {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : ¬ IsSplitAt w) : w ∈ S := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  by_contra h
  exact hw ⟨u, fun e => h (e ▸ hu), hu'⟩

end GlobalTheory.UnitaryClasses
