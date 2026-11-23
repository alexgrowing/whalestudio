import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.MulTupApplyEqSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix

section Equiv

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n M : ℕ}

theorem continuous_mulTup (D : Matrix (Fin n) (Fin n) K) : Continuous (mulTup (M := M) D) := by
  first
  | (unfold mulTup; fun_prop)
  | (simp only [mulTup]; fun_prop)
  | (unfold mulTup; continuity)
  | fun_prop

def tupEquiv (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Fin n → Fin M → K) ≃ₜ+ (Fin n → Fin M → K) where
  toFun := mulTup (D : Matrix (Fin n) (Fin n) K)
  invFun := mulTup (↑D⁻¹ : Matrix (Fin n) (Fin n) K)
  left_inv X := by rw [mulTup_mul, D.mul_inv, mulTup_one]
  right_inv X := by rw [mulTup_mul, D.inv_mul, mulTup_one]
  map_add' := mulTup_add _
  continuous_toFun := continuous_mulTup _
  continuous_invFun := continuous_mulTup _

end Equiv

section HermEquiv

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}

theorem continuous_hermMap [IsTopologicalRing (R ⊗[F] E)] (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (hermMap R σ hσ D) := by
  first
  | (unfold hermMap; fun_prop)
  | (simp only [hermMap]; fun_prop)
  | (unfold hermMap; exact Continuous.subtype_mk (by fun_prop) _)
  | (unfold hermMap; continuity)

def hermEquiv [IsTopologicalRing (R ⊗[F] E)] (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) :
    HermR R σ n ≃ₜ+ HermR R σ n where
  toFun := hermMap R σ hσ D
  invFun := hermMap R σ hσ ↑D⁻¹
  left_inv S := by rw [hermMap_mul, D.mul_inv, hermMap_one]
  right_inv S := by rw [hermMap_mul, D.inv_mul, hermMap_one]
  map_add' S T := Subtype.ext (by simp [hermMap_coe, Matrix.mul_add, Matrix.add_mul])
  continuous_toFun := continuous_hermMap R σ hσ _
  continuous_invFun := continuous_hermMap R σ hσ _

end HermEquiv

section Haar

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem map_eq_smul (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ G) :
    μ.map e = (((addEquivAddHaarChar e)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by
  have h := MeasureTheory.addEquivAddHaarChar_smul_map μ e
  have hc : (addEquivAddHaarChar e : ℝ≥0) ≠ 0 := (MeasureTheory.addEquivAddHaarChar_pos e).ne'
  conv_rhs => rw [← h]
  rw [ENNReal.smul_def (addEquivAddHaarChar e), smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc,
    ENNReal.coe_one, one_smul]

end Haar

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]

def cTup (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  (addEquivAddHaarChar (tupEquiv (M := M) D))⁻¹

def cHerm (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  addEquivAddHaarChar (hermEquiv R σ hσ (n := n) D)

include hJ in

theorem fib_map_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀) :
    (fib S₀).map (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ((cTup (M := M) R D : ℝ≥0∞) *
        (cHerm σ hσ R D : ℝ≥0∞)) • fib S₀ := by
  let e := tupEquiv (M := M) D
  let h := hermEquiv R σ hσ D
  have hμ : μ.map e.toHomeomorph = (cTup (M := M) R D : ℝ≥0∞) • μ :=
    map_eq_smul μ e
  have hν : ν.map h.toHomeomorph.symm = (cHerm σ hσ R D : ℝ≥0∞) • ν := by
    have := map_eq_smul ν h.symm
    rw [addEquivAddHaarChar_symm, inv_inv] at this
    exact this
  have := fib_map_fixed e.toHomeomorph h.toHomeomorph (f' := gramH R σ hσ J hJ)
    (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)
    (fun X => gramH_mulTup_of hG R σ hσ J hJ _ X) (preimage_linIndep D) ENNReal.coe_ne_top
    ENNReal.coe_ne_top hμ hν hfib S₀ hS₀
  exact this

include hJ in

theorem fib_image_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀)
    (A : Set (Fin n → Fin M → R ⊗[F] E)) :
    ((cTup (M := M) R D : ℝ≥0∞) * (cHerm σ hσ R D : ℝ≥0∞)) *
      fib S₀ (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) '' A) = fib S₀ A := by
  have hmap := fib_map_mulTup (hJ := hJ) (hG := hG) (hU := hU) (hL := hL) (hfib := hfib) (hS₀ := hS₀)
  have inj : Function.Injective (tupEquiv (M := M) D) := (tupEquiv (M := M) D).injective
  have e1 := MeasurableEquiv.map_apply (μ := fib S₀)
    ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv) ((tupEquiv (M := M) D) '' A)
  have e2 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) ⁻¹'
      ((tupEquiv (M := M) D) '' A) = A := Set.preimage_image_eq A inj
  rw [e2] at e1
  have e3 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) =
      mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  have e4 : ((tupEquiv (M := M) D) : _ → _) = mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  rw [e3, e4, hmap, Measure.smul_apply, smul_eq_mul] at e1
  exact e1

end Cov

end PI.DegenerateSiegelWeil.Scale
