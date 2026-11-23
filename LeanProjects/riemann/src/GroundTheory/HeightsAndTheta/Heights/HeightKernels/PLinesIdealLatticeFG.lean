import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealLatticeFG

theorem idealLattice_eq_iSup (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) :=
  (Submodule.iSup_map_single).symm

theorem fg (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by
  rw [idealLattice_eq_iSup]
  exact Submodule.fg_iSup _ fun x =>
    ((a x).fg_of_isNoetherianRing le_rfl).map _

theorem single_mem_span (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by
  have hbot : (a x : Submodule (𝓞 K) K) ≠ ⊥ := by
    rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hmem : (Pi.single x y : Fin n → K) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    by_cases h : i = x
    · subst h; simpa using hy
    · simp [h]
  have heq : (Pi.single x 1 : Fin n → K) = y⁻¹ • (Pi.single x y : Fin n → K) := by
    ext i
    by_cases h : i = x
    · subst h; simp [hy0]
    · simp [h]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end KLinesIdealLatticeFG

open KLinesIdealLatticeFG in

theorem LinesIdealLatticeFG.proof : LinesIdealLatticeFG.Statement := by
  intro K _ _ n a ha
  refine ⟨fg K a, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_span K a x (ha x)

end GroundTheory.Heights₂.Heights
