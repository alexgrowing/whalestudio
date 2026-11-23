import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_GLint_iff_entries_cell {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} :
    x ∈ GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem isOpen_intAway (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E} := by
  refine RestrictedProduct.isOpen_forall_imp_mem (fun v => ?_)
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem isOpen_US (S : Finset (HeightOneSpectrum (𝓞 E))) : IsOpen (US E n S : Set (GA E n)) := by
  set A := {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E}
  have e : (US E n S : Set (GA E n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, ((fun g : GA E n => ((g : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A ∩
        (fun g : GA E n => (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A) := by
    ext g
    simp only [SetLike.mem_coe, US, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, A, Set.mem_setOf_eq, GlobalTheory.LFun.KGL, mem_GLint_iff_entries_cell, ← map_inv]
    constructor
    · intro h i j
      exact ⟨fun v hv => (h v hv).1 i j, fun v hv => (h v hv).2 i j⟩
    · intro h v hv
      exact ⟨fun i j => (h i j).1 v hv, fun i j => (h i j).2 v hv⟩
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))

theorem isOpen_adelicUnipotentTimesIntegralOutsideSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  intro E _ _ n S
  have e : C0 E n S = ⋃ u ∈ (NA E n : Set (GA E n)), (fun k => u * k) '' (US E n S : Set (GA E n)) := by
    ext g
    simp only [C0, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
  rw [e]
  exact isOpen_biUnion fun u _ => isOpenMap_mul_left u _ (isOpen_US S)

end GlobalTheory.CellDec
