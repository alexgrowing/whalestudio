import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]

def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
