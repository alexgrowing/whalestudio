import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealIndexPos

variable {K : Type} [Field K] [NumberField K]

noncomputable def toOne (K : Type) [Field K] : K →ₗ[𝓞 K] (Unit → K) :=
  LinearMap.pi fun _ => LinearMap.id

omit [NumberField K] in
theorem toOne_injective : Function.Injective (toOne K) := fun _ _ h =>
  congrFun h ()

theorem fg_and_span (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ).FG ∧
      Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) : Submodule (𝓞 K) (Unit → K)) :
        Set (Unit → K)) = ⊤ := by
  refine ⟨((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map _).restrictScalars, ?_⟩
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine eq_top_iff.mpr fun v _ => ?_
  have hmem : toOne K x ∈ Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) :
      Submodule (𝓞 K) (Unit → K)) : Set (Unit → K)) :=
    Submodule.subset_span (Submodule.mem_map_of_mem hxJ)
  have hv : v = (v () / x) • toOne K x := by
    funext u
    simp [toOne, div_mul_cancel₀ _ hx0]
  rw [hv]
  exact Submodule.smul_mem _ _ hmem

end KLinesIdealIndexPos

open KLinesIdealIndexPos in

theorem LinesIdealIndexPos.proof (h1 : LinesIsLattice.Statement) (h2 : LinesGenIndexTrans.Statement) :
    LinesIdealIndexPos.Statement := by
  intro K _ _ I hI
  have hL : ∀ J : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 →
      Submodule.IsLattice ℚ (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ) :=
    fun J hJ => h1 K Unit _ (fg_and_span J hJ).1 (fg_and_span J hJ).2
  have hpos := (h2 (Unit → K) _ _ _ (hL I hI) (hL 1 one_ne_zero) (hL 1 one_ne_zero)).1
  have hmap : ∀ A B : AddSubgroup K, genIndex (A.map ((toOne K : K →+ (Unit → K))))
      (B.map (toOne K : K →+ (Unit → K))) = genIndex A B := by
    intro A B
    have hinj : Function.Injective (toOne K : K →+ (Unit → K)) := toOne_injective
    simp only [genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  rw [FractionalIdeal.coe_one] at hpos
  unfold idealIndex
  rw [← hmap]
  exact hpos

end GroundTheory.Heights₂.Heights
