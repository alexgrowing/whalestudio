import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermTensor
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Patch

abbrev Amb : Type 1 := Σ (K : Type) (_ : Fintype K) (ι : K → Type), ∀ k, Fintype (ι k)

abbrev AmbFam (a : Amb) : Type :=
  letI := a.2.1; letI := a.2.2.2
  Ideal (MRing a.2.2.1) → (n : ℕ) → (Fin n → HermLine a.2.2.1) → ℝ

def AmbIsFam (a : Amb) (F : AmbFam a) : Prop :=
  letI := a.2.1; letI := a.2.2.2
  IsIntersectionFamily (ι := a.2.2.1) F

open Classical in

def patchFam (J : AllFam) (a : Amb) (F : AmbFam a) : AllFam :=
  fun K _ ι _ => if h : (⟨K, ‹_›, ι, ‹_›⟩ : Amb) = a then cast (congrArg AmbFam h.symm) F else J K ι

end Patch

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_projBundleIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) = P := by
  have key : (projBundleMap P B).comp
      (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · have hC := RingHom.ext_int
        (((projBundleMap P B).comp
          (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C)
        (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
          ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)
      exact RingHom.congr_fun hC r
    · obtain ⟨k, i⟩ := p
      simp [projBundleMap, inlV, genPt]
  ext f
  change projBundleMap P B ((rename (inlV (ι₂ := fun _ : Unit => Fin N1)) :
      MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom f) = 0 ↔ f ∈ P
  rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.C_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

end Lemmas

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end GroundTheory.Heights₂.Heights.Inter
