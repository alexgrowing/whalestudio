import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem gl_det_eq_one_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (M := (g : Matrix (Fin r) (Fin r) κ))
    (fun i j h => unip_lower hg h)]
  simp [unip_diag hg]

theorem chi_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.IsGrp F) :
    ∀ i, ∀ u ∈ F.P0, (R.FW i).chi u = 1 := by
  intro i u hu
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simpa using hu
  rw [h1] at h2
  apply Units.ext
  apply D.what₂.embLL.injective
  rw [h.chiW i u, Units.val_one, map_one]
  refine Finset.prod_eq_one fun PP _ => ?_
  rw [gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)), map_one, Units.val_one]

end GlobalTheory.TraceIncl
