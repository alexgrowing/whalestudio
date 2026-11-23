import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace TopDualLatticeChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def supStandard (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice ⊔ (HermLattice.standard K i).lattice
  fg := F.fg.sup (HermLattice.standard K i).fg
  span_eq := eq_top_iff.mpr (F.span_eq ▸ Submodule.span_mono
    (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

omit [NumberField K] in

theorem gramAt_one_single (σ : K →+* ℂ) :
    gramAt (1 : Matrix (Fin i) (Fin i) ℂ) σ (fun j : Fin i => (Pi.single j 1 : Fin i → K)) = 1 := by
  ext a c
  simp only [gramAt, embVec, Matrix.one_mulVec, dotProduct, Pi.star_apply, Pi.single_apply,
    apply_ite σ, map_one, map_zero, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem standard_degree : (HermLattice.standard K i).degree = 0 := by
  have hinf : (HermLattice.standard K i).lattice ⊓
      (Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K))).restrictScalars (𝓞 K) =
      (HermLattice.standard K i).lattice :=
    inf_eq_left.mpr (Submodule.span_le_restrictScalars (𝓞 K) K _)
  simp only [HermLattice.degree, subDegree, hinf]
  have hstd : (HermLattice.standard K i).metric = fun _ => 1 := rfl
  simp only [hstd, gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero, genIndex]
  show Real.log (((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
    (HermLattice.standard K i).lattice.toAddSubgroup : ℝ) /
      ((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
        (HermLattice.standard K i).lattice.toAddSubgroup : ℝ)) = 0
  simp [AddSubgroup.relIndex_self]

end TopDualLatticeChange

open TopDualLatticeChange in

theorem DualTopLatticeChange.proof (hSub : DualTopSubLattice.Statement) :
    DualTopLatticeChange.Statement := by
  intro K _ _ i F T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨TG, hTG, hdTG, ⟨bG⟩⟩ := DualLatticeBasisExists.proof K i (supStandard F)
  have hbG := DualEmbBijective.proof K i (supStandard F) TG bG
  have h1 := hSub K i (supStandard F) F TG T bG hbG b hb II hi hII le_sup_left
  have h2 := hSub K i (supStandard F) (HermLattice.standard K i) TG T' bG hbG b' hb' II hi hII
    le_sup_right
  have hstd : (HermLattice.standard K i).withStdMetric.degree = 0 := standard_degree
  have hline : dualLine (HermLattice.standard K i).withStdMetric b' hb' =
      dualLine (HermLattice.standard K i) b' hb' := rfl
  rw [hline, hstd] at h2
  rw [h1, h2]
  ring

end

end GroundTheory.Heights₂.Heights
