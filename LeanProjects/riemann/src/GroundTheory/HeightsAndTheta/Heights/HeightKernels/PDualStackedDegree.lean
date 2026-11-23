import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace DualStackedDegreeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem isLattice (F : HermLattice K i) : Submodule.IsLattice ℚ (F.lattice.restrictScalars ℤ) :=
  LinesIsLattice.proof K (Fin i) F.lattice (F.fg.restrictScalars) F.span_eq

theorem degree_withStdMetric (F : HermLattice K i) :
    F.withStdMetric.degree = Real.log (genIndex F.lattice.toAddSubgroup
      (HermLattice.standard K i).lattice.toAddSubgroup) := by
  have hspan : Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) =
        Set.range (Pi.basisFun K (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]; exact (Pi.basisFun K (Fin i)).span_eq
  have hlat : F.withStdMetric.lattice = F.lattice := rfl
  have hstd : F.withStdMetric.metric = fun _ => 1 := rfl
  simp only [HermLattice.degree, subDegree, hlat, hstd, hspan, Submodule.restrictScalars_top, inf_top_eq,
    TopDualLatticeChange.gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero]
  rfl

theorem degree_sub (F F' : HermLattice K i) (h : F'.lattice ≤ F.lattice) :
    F.withStdMetric.degree - F'.withStdMetric.degree =
      Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup) := by
  have hT := LinesGenIndexTrans.proof LinesLatticeBasis.proof
    (LinesGenIndexDet.proof LinesLatticeBasis.proof)
  obtain ⟨hpos1, hmul⟩ := hT (Fin i → K) (F.lattice.restrictScalars ℤ) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F) (isLattice F') (isLattice _)
  obtain ⟨hpos2, -⟩ := hT (Fin i → K) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F') (isLattice _) (isLattice _)
  have e : ∀ L : Submodule (𝓞 K) (Fin i → K), (L.restrictScalars ℤ).toAddSubgroup = L.toAddSubgroup :=
    fun _ => rfl
  simp only [e] at hpos1 hmul hpos2
  rw [degree_withStdMetric, degree_withStdMetric, ← hmul, Real.log_mul hpos1.ne' hpos2.ne',
    add_sub_cancel_right, genIndex, (AddSubgroup.relIndex_eq_one (H := F.lattice.toAddSubgroup)
      (K := F'.lattice.toAddSubgroup)).mpr (fun _ hx => h hx), Nat.cast_one, div_one]

theorem relIndex_stacked {T : Type} [Fintype T] [DecidableEq T] {F F' : HermLattice K i}
    (h : F'.lattice ≤ F.lattice) (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ)
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) :
    ((dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup : ℝ) = ∏ t, |(a t : ℝ)| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ (DualTopStackedExistence.dualLattice_mono h) b b']
  have hv : (fun t => (⟨(b t : Fin i → K), DualTopStackedExistence.dualLattice_mono h (b t).2⟩ :
      dualLattice F')) = fun t => a t • b' t := by
    funext t; exact Subtype.ext (hab t)
  have hdet : b'.det (fun t => a t • b' t) = ∏ t, a t := by
    rw [Module.Basis.det_apply]
    have hm : b'.toMatrix (fun t => a t • b' t) = Matrix.diagonal a := by
      ext s t
      by_cases hst : s = t
      · subst hst; simp [Module.Basis.toMatrix_apply]
      · simp [Module.Basis.toMatrix_apply, hst]
    rw [hm, Matrix.det_diagonal]
  erw [hv, hdet]
  push_cast [Nat.cast_natAbs, Int.cast_abs, Int.cast_prod, Finset.abs_prod]
  rfl

end DualStackedDegreeAlt

open DualStackedDegreeAlt in

theorem DualStackedDegree.proof (hIdx : DualLatticeIndex.Statement) : DualStackedDegree.Statement := by
  intro K _ _ i F F' T _ _ b b' a h hab
  have ha : ∀ t, a t ≠ 0 := fun t ht => b.ne_zero t (Subtype.ext (by rw [hab t, ht, zero_smul]; rfl))
  rw [degree_sub F F' h, ← hIdx K i F F' h, relIndex_stacked h b b' a hab,
    Real.log_prod (fun t _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha t)))]

end

end GroundTheory.Heights₂.Heights
