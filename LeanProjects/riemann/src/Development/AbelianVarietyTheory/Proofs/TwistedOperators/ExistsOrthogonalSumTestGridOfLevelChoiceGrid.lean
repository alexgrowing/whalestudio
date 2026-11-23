import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem hT_eq_coords (S : HSp D) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.BasicNotions.HSpace.gram]
  ring

theorem hT_cols (S : HSp D) {k l : ℕ} (a : Matrix (Fin S.rank) (Fin k) D.host.E) (b : Matrix (Fin S.rank) (Fin l) D.host.E)
    (q : Fin k) (p : Fin l) :
    S.hT (S.frame.equivFun.symm (fun i => a i q)) (S.frame.equivFun.symm (fun i => b i p)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) a * S.gram * b) q p := by
  rw [hT_eq_coords]
  have e1 : ∀ v : Fin S.rank → D.host.E, S.frame.repr (S.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [e1, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_orthogonalSum_testGrid_of_levelChoiceGrid {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E}
    (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) (_hε : ε = 1 ∨ ε = -1)
    (hΛ : B.Λ = d.lat A.Λ 𝔟) :
    ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  refine ⟨⟨d.ι, fun p => B.V.frame.equivFun.symm (fun k => d.a k p)⟩, rfl, ?_⟩
  have e1 : ∀ v : Fin B.V.rank → D.host.E, B.V.frame.repr (B.V.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨d.isom, ?_, ?_, d.rank, ?_⟩
  ·
    intro x p
    show B.V.hT _ (d.ι x) = 0
    conv_lhs => rw [← A.V.frame.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := B.V.herm.eq (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p))
    have h2 : d.ι (A.V.frame k) = B.V.frame.equivFun.symm (fun i => frameMat B.V A.V d.ι i k) := by
      apply B.V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [frameMat, LinearMap.toMatrix_apply]
    have h3 : B.V.hT (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p)) = 0 := by
      rw [h2, hT_cols, d.perp]; rfl
    rw [← h1, h3]
    simp
  ·
    intro p q
    show B.V.hT _ _ = _
    rw [hT_cols, d.gram]
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff]; omega) | simp_all
  ·
    have key : ∀ (x : A.V.V) (t : Fin c → D.host.E),
        B.V.frame.equivFun (d.ι x + ∑ p, t p • B.V.frame.equivFun.symm (fun k => d.a k p)) =
          frameMat B.V A.V d.ι *ᵥ A.V.frame.equivFun x + d.a *ᵥ t := by
      intro x t
      rw [map_add, map_sum]
      congr 1
      · simp only [Module.Basis.equivFun_apply, frameMat]
        exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
      · simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    intro y
    show B.V.frame.equivFun y ∈ B.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨z, hz, u, hu, hy⟩
      refine ⟨A.V.frame.equivFun.symm z, ?_, u, hu, ?_⟩
      · show A.V.frame.equivFun (A.V.frame.equivFun.symm z) ∈ A.Λ
        rwa [LinearEquiv.apply_symm_apply]
      · apply B.V.frame.equivFun.injective
        rw [key, LinearEquiv.apply_symm_apply]
        exact hy
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨A.V.frame.equivFun x, hx, t, ht, key x t⟩

example : ∀ {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D), (ε = 1 ∨ ε = -1) → B.Λ = d.lat A.Λ 𝔟 → ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  intro D A B c ε d 𝔟 h hΛ
  exact exists_orthogonalSum_testGrid_of_levelChoiceGrid A B d 𝔟 h hΛ

end GlobalTheory.GridJoin

end
