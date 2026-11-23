import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapTraceEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLattiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairingStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypPairSelfDual

theorem exists_partner : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  intro D S Λ x hΛ hx0 hxx
  set σ : D.host.E →ₐ[D.host.F] D.host.E := D.sp.cm.sig with hσdef
  have hσs : ∀ e : D.host.E, σ e = star e := fun _ => rfl
  have hσ : ∀ e, σ (σ e) = e := fun e => by rw [hσs, hσs, star_star]
  set J : Matrix (Fin S.rank) (Fin S.rank) D.host.E := Matrix.transpose (HSpace.gram S) with hJ
  set co : S.V ≃ₗ[D.host.E] (Fin S.rank → D.host.E) := S.frame.equivFun with hco

  have hform : ∀ a b : S.V, S.hT a b = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co b) (co a) := fun a b => by
    rw [GlobalTheory.RelFlag.hT_eq_form]
    simp only [GlobalTheory.SgAlg.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IntPair.co, dotProduct, Matrix.mulVec, hJ,
      Matrix.transpose_apply, hσs, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hco]; ring
  have hframe : ∀ i, co (S.frame i) = Pi.single i 1 := fun i => by
    ext j; simp [hco, Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hherm : ∀ i j, σ (J j i) = J i j := fun i j => by
    have h1 := S.herm.eq (S.frame i) (S.frame j)
    have e1 : S.hT (S.frame i) (S.frame j) = J j i := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    have e2 : S.hT (S.frame j) (S.frame i) = J i j := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e1, e2] at h1
    rw [hσs]; simpa [starRingEnd_apply] using h1
  have hfg : Λ.FG := hΛ.1.fg
  have hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v) := fun w => by
    rw [hΛ.2 w]
    refine forall₂_congr fun v _ => ?_
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v = ∑ i, ∑ j, star (v i) * S.gram i j * w j := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, hJ, Matrix.transpose_apply, hσs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← GlobalTheory.PlaneSplit.mem_range_iff]
    simp [RingHom.mem_range, eq_comm]
  have hfu : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := GlobalTheory.HeckeAdjoint.unramified_host D; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E σ
    (GlobalTheory.AdelicU.isCMExt_host D) hfu
  have hcx0 : co x ≠ 0 := fun h => hx0 (co.injective (by rw [h, map_zero]))
  have hcxx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co x) (co x) = 0 := by rw [← hform]; exact hxx
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing D.host.F D.host.E σ hσ S.rank J Λ hfg hherm hdual (co x) hcx0
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module D.host.F D.host.E σ S.rank J Λ hfg (co x) ⟨z0, hz0L, hz0⟩
  obtain ⟨y, hyy, hxy, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice D.host.F D.host.E σ hσ S.rank J Λ hherm hdual θ hθ (co x) y₀ hcxx hy₀1 hy₀L
  have hconj : ∀ a b, σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun a b => by
    have hh' : ∀ i j, σ (J i j) = J j i := fun i j => hherm j i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hh']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨co.symm y, ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hform, co.apply_symm_apply]; exact hyy
  · rw [hform, co.apply_symm_apply, ← hconj, hxy, map_one]
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform, co.apply_symm_apply]
    exact (hL _ hz).1
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform]
    change _ • co (co.symm y) ∈ Λ
    rw [co.apply_symm_apply]
    exact (hL _ hz).2

end GlobalTheory.HypPairSelfDual
