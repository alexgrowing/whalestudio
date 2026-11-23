import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.LiftOntoGood

theorem mem_range_of_fixed {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (hsa : LinearMap.adjoint e = e) (hid : e * e = e) (hfix : ∀ y, e (th y) = th y)
    (hinj : ∀ v, e v = v → LinearMap.adjoint th v = 0 → v = 0) (x : Y) (hx : e x = x) : x ∈ LinearMap.range th := by
  have hcomp : e ∘ₗ th = th := LinearMap.ext hfix
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range th)]
  intro v hv
  have hv0 : LinearMap.adjoint th v = 0 := by
    refine ext_inner_left ℂ fun z => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hv _ (LinearMap.mem_range_self _ z)
  have h1 : LinearMap.adjoint th (e v) = 0 := by
    have e2 : LinearMap.adjoint th (e v) = LinearMap.adjoint (e ∘ₗ th) v := by
      rw [LinearMap.adjoint_comp, hsa, LinearMap.comp_apply]
    rw [e2, hcomp, hv0]
  have h2 : e (e v) = e v := by rw [← Module.End.mul_apply, hid]
  have h3 : e v = 0 := hinj (e v) h2 h1
  rw [← hx, ← LinearMap.adjoint_inner_left, hsa, h3, inner_zero_left]

set_option maxHeartbeats 1000000 in

theorem goodW_le_range : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp _ _ hU j
  have hM : R.toRealDat.IsModels := hC.base.models
  have hC3 := RealDat3.characterisation_of_weak hC hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hsa : LinearMap.adjoint (GlobalTheory.Hk3.eH R.toRealDat j) = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.LiftScalarL.adjoint_eH R.toRealDat hM hX j
  have hc : ∀ g, ∑ a, RealDat.eC (A := A3.A) (sg0 D A3.A) a * RealDat.eC (A := A3.A) (sg0 D A3.A) (a⁻¹ * g) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g := fun g => GlobalTheory.Hk3.conv_map_idem _ (idemOf_mul_self A3.A.X hX) (sg0 D A3.A) g
  have hidem : GlobalTheory.Hk3.eH R.toRealDat j * GlobalTheory.Hk3.eH R.toRealDat j = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.Hk3.sum_rep_idem _ _ hc
  have hinj := (hM.HW j (sg0 D A3.A)).1
  have hrange := (hM.HW j (sg0 D A3.A)).2.1
  have hfixth : ∀ y, GlobalTheory.Hk3.eH R.toRealDat j (R.thG j A3.A.μ0 y) = R.thG j A3.A.μ0 y := by
    intro y
    have hm := hC3.thP.thF_mem j A3.A.μ0 y
    rw [← hrange] at hm
    obtain ⟨x0, hx0⟩ := hm
    have e1 : R.thG j A3.A.μ0 y = GlobalTheory.Hk3.eH R.toRealDat j x0 := by
      apply hinj
      rw [hC3.thP.thG j A3.A.μ0 y, ← hx0, GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j x0]
    rw [e1, ← Module.End.mul_apply, hidem]
  have key := mem_range_of_fixed (R.thG j A3.A.μ0) (GlobalTheory.Hk3.eH R.toRealDat j) hsa hidem hfixth (hUp j A3.A.μ0)
  intro w hw
  have hw' : w ∈ LinearMap.range ((R.toCx3 F).w0C false j) := hw
  rw [GlobalTheory.LevelRange.range_w0C_eq R F hOk hC hU false j] at hw'
  obtain ⟨x, rfl⟩ : ∃ x : (R.HW j (sg0 D A3.A)).H, Tw.mk (twAt D.what₂.embLL A3.A.v0) x = w := ⟨w, rfl⟩
  have hgood : (R.HW j (sg0 D A3.A)).e x ∈
      R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := hw'
  have hfix : GlobalTheory.Hk3.eH R.toRealDat j x = x := by
    apply hinj
    rw [GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j]
    exact GlobalTheory.LiftScalarCompare.postOn_of_good hgood
  obtain ⟨y, hy⟩ := key _ hfix
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hC.phase j).1, norm_zero] at this
    exact one_ne_zero this
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y), ?_⟩
  show cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.μ0 ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y) = x
  rw [map_smul, smul_inv_smul₀ hne, hy]

end GlobalTheory.LiftOntoGood
