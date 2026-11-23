import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTupleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevelStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamLab

theorem adj_eig {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (θ : X →ₗ[ℂ] Y) (c : ℝ) (x₀ : X)
    (h : ∀ x', ⟪θ x₀, θ x'⟫_ℂ = (c : ℂ) * ⟪x₀, x'⟫_ℂ) : θ (LinearMap.adjoint θ (θ x₀)) = (c : ℂ) • θ x₀ := by
  have ha : LinearMap.adjoint θ (θ x₀) = (c : ℂ) • x₀ := by
    refine ext_inner_right ℂ fun x' => ?_
    rw [LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]
  rw [ha, map_smul]

theorem eigenvalue_eq_of_label : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.R3.LamLab
