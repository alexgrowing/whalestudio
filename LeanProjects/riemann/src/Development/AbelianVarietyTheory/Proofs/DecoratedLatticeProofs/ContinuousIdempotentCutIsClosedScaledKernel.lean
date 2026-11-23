import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem continuous_mt_cutTop (V : HSp D) : Continuous (fun g : GA D V => Formalism.L2.Theta.mt V g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) :
    Continuous (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  refine continuous_matrix fun i j => ?_
  have h : (fun g : GA D V => Formalism.L2.Theta.mt V (cutG V ε hε g) i j) = fun g : GA D V =>
      ε • Formalism.L2.Theta.mt V g i j +
        ((1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) i j := by
    funext g
    rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def ε]
  rw [h]
  exact (((continuous_mt_cutTop V).matrix_elem i j).const_smul ε).add continuous_const

theorem continuous_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : Continuous (cutG V ε hε) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨continuous_mt_cutG V ε hε, ?_⟩)
  have h := (continuous_mt_cutG V ε hε).comp (continuous_inv (G := GA D V))
  refine h.congr fun g => ?_
  rw [Function.comp_apply, map_inv]
  rfl

theorem isClosed_smul_sub_one_eq_zero (V : HSp D) (c : AF D.host.F) :
    IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e.isEmbedding.t2Space
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI hs : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  haveI : ContinuousConstSMul (AF D.host.F) (AE D) :=
    @ContinuousSMul.continuousConstSMul (AF D.host.F) (AE D) _ _ _ hs
  have h : {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} =
      ⋂ i, ⋂ j, {g : GA D V | c • Formalism.L2.Theta.mt V g i j =
        c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero, Algebra.smul_def, Algebra.smul_def]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (((continuous_mt_cutTop V).matrix_elem i j).const_smul c) continuous_const

theorem continuous_cutG_and_isClosed : ∀ (D : D7) (V : HSp D), (∀ (ε : AF D.host.F) (hε : ε * ε = ε), Continuous (GlobalTheory.FinPl.SetCut.cutG V ε hε)) ∧ ∀ c : AF D.host.F, IsClosed {g : GA D V | ∀ i j, algebraMap (AF D.host.F) (AE D) c * (Formalism.L2.Theta.mt V g - 1) i j = 0} :=
  fun _ V => ⟨continuous_cutG V, isClosed_smul_sub_one_eq_zero V⟩

end GlobalTheory.FinPl.SetCut
