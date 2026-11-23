import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.AnisoRange

theorem bddAbove_isotropic_dims {D : D7} (V : HSp D) :
    BddAbove {k | ∃ W : Submodule D.host.E V.V, Module.finrank D.host.E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, V.hT x y = 0} := by
  haveI := V.fd
  refine ⟨Module.finrank D.host.E V.V, ?_⟩
  rintro k ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

theorem one_le_wittIdx {D : D7} (V : HSp D) {v : V.V} (hv : v ≠ 0) (h : V.hT v v = 0) :
    1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  refine le_csSup (bddAbove_isotropic_dims V) ⟨Submodule.span D.host.E {v}, finrank_span_singleton hv, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [h]

theorem hT_coord {D : D7} (V : HSp D) (x : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm x) =
      HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x := by
  have hσ : ∀ a : D.host.E, ((D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) a = star a :=
    fun _ => rfl
  simp only [Module.Basis.equivFun_symm_apply, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, HSpace.gram]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem anisoOfRange : PositivityTheory.PfSWUS.AnisoOfRange := by
  rintro D n V ⟨h1, -, h3⟩
  by_cases h : n + 2 ≤ V.rank
  · exact Or.inl h
  refine Or.inr fun x hx => ?_
  by_contra hne
  have hv : V.frame.equivFun.symm x ≠ 0 := fun h0 => hne ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 h0)
  have := one_le_wittIdx V hv ((hT_coord V x).trans hx)
  omega

end GlobalTheory.CompanionTheory.AnisoRange
