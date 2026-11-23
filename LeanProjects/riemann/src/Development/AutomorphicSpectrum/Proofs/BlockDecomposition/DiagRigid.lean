import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagRigid

theorem diag_rigid : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ (d d' : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → (∀ i, ordL (d' i : L) = y i) → ∀ h : GL (Fin n) L, h⁻¹ * GlobalTheory.SmGL.diagT L (Fin n) d * h = GlobalTheory.SmGL.diagT L (Fin n) d' → d = d' ∧ ∃ s : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) s := by
  intro L _ _ n y hy d d' hd hd' h hh
  have key : GlobalTheory.SmGL.diagT L (Fin n) d * h = h * GlobalTheory.SmGL.diagT L (Fin n) d' := by
    rw [← hh]; simp only [mul_assoc, mul_inv_cancel_left]
  have key' : (Matrix.diagonal fun i => (d i : L)) * (h : Matrix (Fin n) (Fin n) L)
      = (h : Matrix (Fin n) (Fin n) L) * Matrix.diagonal fun i => (d' i : L) := by
    have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L)) key
    simpa only [Units.val_mul, GlobalTheory.SmGL.val_diagT] using this
  have ent : ∀ i j, (d i : L) * (h : Matrix (Fin n) (Fin n) L) i j
      = (h : Matrix (Fin n) (Fin n) L) i j * (d' j : L) := by
    intro i j
    have := congrFun (congrFun key' i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have off : ∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    by_contra hne
    have e : (d i : L) = (d' j : L) := by
      have := ent i j
      rw [mul_comm] at this
      exact mul_left_cancel₀ hne this
    apply hij
    apply hy
    rw [← hd i, ← hd' j, e]
  have hdiag : (h : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal fun i => (h : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact off i j hij
  have hdet : ∏ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    have h1 : IsUnit (h : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [hdiag, Matrix.det_diagonal] at h1
    simpa [Matrix.diagonal_apply_eq] using h1.ne_zero
  have hii : ∀ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  refine ⟨?_, fun i => Units.mk0 _ (hii i), ?_⟩
  · funext i
    apply Units.ext
    have := ent i i
    rw [mul_comm] at this
    exact mul_left_cancel₀ (hii i) this
  · apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    simpa using hdiag

end GlobalTheory.CompanionTheory.DiagRigid
