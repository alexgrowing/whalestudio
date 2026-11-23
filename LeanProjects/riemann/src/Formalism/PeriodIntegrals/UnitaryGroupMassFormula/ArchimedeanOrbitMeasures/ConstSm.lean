import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kPos_holds : KPos := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have hg : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := by
    unfold Formalism.MainNotions.S.AutInst.gaugeU
    exact Finset.prod_pos fun v _ => (hH.2.2.2.1 v).2
  have hv : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k := by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have ht : 0 < Tw u' := by
    unfold Tw
    exact_mod_cast (D.mem u').A.T_prime.pos
  unfold KVal
  exact mul_pos (mul_pos hg (pow_pos hv _)) (zpow_pos ht _)

theorem orbMeas_holds : OrbMeas := fun X u' => measurable_orbM X u'

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def sigLin (σ : E →ₐ[F] E) : (R ⊗[F] E) →ₗ[R] (R ⊗[F] E) where
  toFun := sigR R σ
  map_add' := map_add _
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    simp [sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) :=
  IsModuleTopology.continuous_of_linearMap (sigLin R σ)

theorem isClosed_hermR [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | sigR R σ (S b a) = S a b} := by
    ext S; simp [HermR]; exact Iff.rfl
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
  · exact (continuous_sigR R σ).comp ((continuous_apply a).comp (continuous_apply b))
  · exact (continuous_apply b).comp (continuous_apply a)

end Herm

theorem hermLF_holds : HermLF := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : νinf.IsAddHaarMeasure := hH.2.2.2.2.2.1.1
  have : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (HmI X) :=
    (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds (TI X u' hT)
  exact ⟨K, hKc, hK.measure_lt_top⟩

theorem continuous_gramI {D : D7} (X : HidaSetting D) :
    Continuous (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :
      TupI X → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hs := continuous_sigR (Ainf X.B.I.F) X.B.I.cm.sig
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, Formalism.UG.hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
    ((continuous_apply j).comp (continuous_apply b))

theorem gramMeas_holds : GramMeas := by
  intro D X S hS
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS' : MeasurableSet[(borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).comap Subtype.val] S := by
    rw [← borel_comap]; exact hS
  obtain ⟨A, hA, rfl⟩ := hS'
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.preimage_inter]
  have hg : @Measurable (TupI X) (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) _ (borel _) (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
    let _ : MeasurableSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := borel _
    have : BorelSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := ⟨rfl⟩
    exact (continuous_gramI X).measurable
  have hC : MeasurableSet[borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))]
      ((HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) : AddSubgroup _) : Set _) :=
    MeasurableSet.of_compl (MeasurableSpace.measurableSet_generateFrom
      (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isOpen_compl)
  exact (hg hA).inter (hg hC)

theorem constTest_of_polar (hP : PolarLoc) (hC : PushCont) : ConstTest :=
  constTest_of gramMeas_holds orbMeas_holds kPos_holds hP hC hermLF_holds

end PI.AprimeInfW
