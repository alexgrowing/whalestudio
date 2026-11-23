import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem deg_map_of_isometry (K : Type) [Field K] [NumberField K] (n m : ℕ) (hW : HermFam K (Fin n → K))
    (h : HermFam K (Fin m → K)) (α : (Fin n → K) →ₗ[K] (Fin m → K)) (hα : Function.Injective α)
    (hiso : ∀ σ y z, hW.form σ y z = h.form σ (α y) (α z)) (E : Submodule (𝓞 K) (Fin n → K))
    (hE : E.FG) : deg hW E = deg h (E.map (α.restrictScalars (𝓞 K))) := by
  set β := α.restrictScalars (𝓞 K) with hβ
  have hβinj : Function.Injective β := hα
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map β) (fun i => α (v i)) := by
    refine ⟨fun i => Submodule.mem_map_of_mem (hv.1 i), hv.2.1.map' α (LinearMap.ker_eq_bot.mpr hα), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span K (Set.range v) := hv.2.2 hx
    have : α x ∈ (Submodule.span K (Set.range v)).map α := Submodule.mem_map_of_mem hx'
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hEm : (E.map β).FG := hE.map _
  rw [arakelovDegree_eq_degreeOfFamily hW hE hv, arakelovDegree_eq_degreeOfFamily h hEm hv']
  unfold degreeOfFamily
  have hspan : Submodule.span (𝓞 K) (Set.range (fun i => α (v i))) =
      (Submodule.span (𝓞 K) (Set.range v)).map β := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hidx : ((Submodule.span (𝓞 K) (Set.range (fun i => α (v i)))).toAddSubgroup.relIndex
      (E.map β).toAddSubgroup) =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
    rw [hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hβinj
  have hgram : ∀ σ, h.gram σ (fun i => α (v i)) = hW.gram σ v := by
    intro σ; ext i j; simp [HermFam.gram, hiso]
  rw [hidx]
  simp only [hgram]

end GlobalTheory
