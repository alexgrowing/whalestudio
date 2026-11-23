import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

namespace UpperTheory.Gal.LocD

private theorem sg_diagT {E : Type} [Field E] {n : ℕ} (σ : E ≃+* E) (t : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) t) = diagT E (Fin n) (fun i => Units.map (σ : E →* E) (t i)) := by
  ext i j
  rw [sg_val, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp
  · simp [diagonal_apply_ne _ h]

private theorem absPow_map {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {σ : E ≃+* E} (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hx : ((Units.map (σ : E →* E) x : Eˣ) : E) = σ x := rfl
  have h1 : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    rw [Units.val_mul, hx, map_mul, hσ, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 x.ne_zero
  have h2 := isUnram_absPow E s _ h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

private theorem deltaHalf_map {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) (t : Fin n → Eˣ) :
    deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) (fun i => Units.map (σ : E →* E) (t i))) =
      deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) t) := by
  have hdet : ∀ (u : Fin n → Eˣ) (a : Fin n),
      GeneralLinearGroup.det ((leviTorus E (Fin n) u) a) = u a :=
    fun u a => congrFun ((leviTorus E (Fin n)).symm_apply_apply u) a
  rw [deltaHalf_apply, deltaHalf_apply]
  simp only [hdet]
  exact Finset.prod_congr rfl (fun a _ => absPow_map hσ _ _)

end UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.jacSemi :
    JacSemi := by
  intro E _ _ _ _ n σ hσ V _ _ π A hA t y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hj : ∀ (s : Fin n → Eˣ) (w : V), jacB π s (Submodule.Quotient.mk w) =
      (((deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) s))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (diagT E (Fin n) s) w) : Jacquet π (unipB E (Fin n))) := fun _ _ => rfl
  rw [hj, map_smul, jacA_mk, jacA_mk, hj, hA, sg_diagT, deltaHalf_map hσ]
