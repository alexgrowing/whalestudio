import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DrowsPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LambdaPrimeBasisRowTypePosAtReference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaProjectionAdjointBasisRowEigenvalueStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec

theorem kapOf_of_eigen {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) {κ : ℝ} (hk : 0 < κ) (hn : 0 < n)
    (hP : ∀ σ, 0 < ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ))
    (hT : ∀ σ, S.iiStar (b σ) = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) : ℝ) : ℂ) • b σ) :
    S.kapOf ty = κ := by
  set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef
  have hdet : LinearMap.det S.iiStar = ((κ ^ n * ∏ σ, P σ : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar =
        Matrix.diagonal (fun σ => ((κ * P σ : ℝ) : ℂ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply,
        ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : j = i
      · subst hij; simp [P]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]; simp
    rw [hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hr : S.kapRatio ty = κ ^ n := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hdet, Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ (Finset.prod_pos fun σ _ => hP σ).ne'
  unfold RowSide.kapOf
  rw [hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (y : EE) :
    S.iiStar y = S.iota D.what₂.mu0 (S.eOp D.what₂.mu0 (LinearMap.adjoint (S.iota D.what₂.mu0) y)) := by
  set μ := D.what₂.mu0
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem kapSharp_eq_kap : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → kapSharp D = R.kap := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI
  exact kapOf_of_eigen (RowSide.sharp D) D.what₂.onb D.what₂.ft hH.prim.posScal.1
    (GlobalTheory.Mem.R3.drows_pos D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL)
    (fun σ => Finset.prod_pos (GlobalTheory.Mem.R3.LamPos.lambdaPrime_basis_row_type_pos_at_reference D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))
    (fun σ => (iiStar_apply_eq (RowSide.sharp D) (D.what₂.onb σ)).trans
      (GlobalTheory.T.iotaProjectionAdjoint_basisRow_eigenvalue hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))

end GlobalTheory.KapRec
end
