import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

noncomputable section

namespace GlobalTheory.KerProjGood

theorem starProjection_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V) (hT : ∀ u ∈ S, T u ∈ S) (hTa : ∀ u ∈ S, LinearMap.adjoint T u ∈ S) (z : V) :
    (S.starProjection (T z) : V) = T (S.starProjection z) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (Submodule.coe_mem _)) fun w hw => ?_
  rw [← map_sub, ← LinearMap.adjoint_inner_right]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := S) z
  rw [inner_eq_zero_symm]
  exact h _ (hTa w hw)

end GlobalTheory.KerProjGood

open GlobalTheory.KerProjGood in

theorem GlobalTheory.kerProj_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ hG j y hy
  have hM := hC.base.models
  have hK := RealDat3.kFormL_of (F := F) hM
  have hJ := RealDat3.jIsoL_of (F := F) hM
  set X := R.toCx3 F with hX
  set t := A3.A.fam.μ0
  have sp := lift_embeddings_span hK j t
  have jr : ∀ (g : G) x, X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) :=
    fun g x => X.jL_opL hK j t (Sum.inr g) x

  have hker : ∀ (g : G), ∀ u ∈ LinearMap.ker (X.θ' j t), X.opLC j t (Sum.inr g) u ∈ LinearMap.ker (X.θ' j t) := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have h := congrArg (fun f => f u) (theta_rho (r := (A3.fam3.F.L j t).r) (ρ := fun g => X.opLC j t (Sum.inr g))
      sp jr (fun g x => hG.2 j t g x) g)
    simp only [LinearMap.comp_apply] at h
    rw [h, hu, map_zero]
  have hadj : ∀ g : G, LinearMap.adjoint (X.opLC j t (Sum.inr g)) = X.opLC j t (Sum.inr g⁻¹) := fun g =>
    (X.opLC_adjoint hK F.cv hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f').symm
  have hcomm : ∀ (g : G) z, ((LinearMap.ker (X.θ' j t)).starProjection (X.opLC j t (Sum.inr g) z) : X.FLC j t) =
      X.opLC j t (Sum.inr g) ((LinearMap.ker (X.θ' j t)).starProjection z) := fun g z =>
    starProjection_comm _ _ (hker g) (fun u hu => by rw [hadj]; exact hker g⁻¹ u hu) z
  have hrange : U2.goodL A3 X F.P0 F.ψ0 F.P1 F.ψ1 j = LinearMap.range (opV A3.fam3.base3.v0.embedding
      (fun g => X.opLC j t (Sum.inr g)) (goodAt (A3.fam3.F.lvlA F.P0 F.ψ0).X (A3.fam3.F.lvlA F.P0 F.ψ0).P
        (A3.fam3.F.lvlA F.P0 F.ψ0).ψ)) := by
    show X.goodPartComplexPoints F.cv false j t = _
    unfold CxData.goodPartComplexPoints
    rw [show F.cv.v0L X.zs false j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA F.P0 F.ψ0) from rfl, goodR_eq]
    conv_rhs => rw [LinearMap.range_eq_map, ← sp, Submodule.map_span]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨X.jL j t x, ⟨x, rfl⟩, (j_opF jr _ x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, j_opF jr _ x⟩
  rw [hrange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(LinearMap.ker (X.θ' j t)).starProjection z, ?_⟩
  simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (hcomm g z).symm

end
