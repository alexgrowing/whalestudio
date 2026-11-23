import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WgLift

open Formalism.IndefR.CxPass.LevelOperators

set_option maxHeartbeats 1000000 in

theorem principal_lift_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hW hpos hA hLT hB i
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hch hex
  have hM := hc.models
  have hCore : Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hθ : ∀ t (u : (R.toCx3 F).FLC i t), Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
      cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) := by
    intro t u
    rfl

  have hsub : ∀ t, ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t), y ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
    rintro t _ ⟨u, rfl⟩
    change Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) ∈ LinearMap.range (eH R.toRealDat i)
    rw [hθ]
    exact ⟨cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u), by rw [map_smul, hL.2.2.2]⟩

  have hrng : ∀ t, LinearMap.range ((R.toCx3 F).θ' i t) ≤
      LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t) := by
    intro t
    obtain ⟨N, ψ, hψ, hr⟩ := hLT i
    have hRZ := Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (F.cv.hL i t)
      (Formalism.IndefR.Cx.CxData.bL (A := A3.fam3.amb3) i t)
      (hK i t).1 (hK i t).2 (hJ i t) ((R.toCx3 F).θ' i t) ψ hψ (fun k x => hr t k x)
    have hgood : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ≤
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
      intro z hz
      have h1 : z ∈ (A3.A.fam.L i t).goodF A3.A.X := (hB.2 i t hz).2
      have h2 : (A3.A.fam.L i t).goodF A3.A.X = LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
        unfold BlockDat.goodF
        rw [Formalism.IndefR.CxPass.LevelOperators.goodAt_bot]
        rfl
      rwa [h2] at h1
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, k, hk, hak⟩ := (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).exists_add_mem_mem_orthogonal v
    have hk0 : (R.toCx3 F).θ' i t k = 0 := by
      have h0 : ⟪LinearMap.adjoint ((R.toCx3 F).θ' i t) ((R.toCx3 F).θ' i t k), k⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hk _ ⟨_, rfl⟩
      rw [LinearMap.adjoint_inner_left] at h0
      exact inner_self_eq_zero.1 h0
    rw [hak, map_add, hk0, add_zero]
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) (A3.A.fam.lvlA ⊥ 1) _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq,
        show goodAt (A3.A.fam.lvlA ⊥ 1).X (A3.A.fam.lvlA ⊥ 1).P (A3.A.fam.lvlA ⊥ 1).ψ = idemOf A3.A.X from
          Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _]
      rfl
    have hZ2 : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := (inf_eq_left.2 hgood).symm.trans hZeq
    rw [← hRZ, hZ2] at hu
    obtain ⟨c, hc⟩ : u ∈ LinearMap.range (lin ((R.toCx3 F).uL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) := by
      refine (Submodule.span_le.2 ?_) hu
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x,
        ((R.toCx3 F).jL_toL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t x).symm⟩
    exact ⟨c, by rw [(R.toCx3 F).tC_eq, hc]⟩

  have hsup : Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ≤ LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0) := by
    intro w hw
    have hw' : Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by rw [hW i]; exact hw
    have hcc : starRingEnd ℂ (R.phs i) * R.phs i = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, (hch.phase i).1]; norm_num
    refine Submodule.iSup_induction (fun p => R.Wp3 i p) (motive := fun (x : (R.HW i (sg0 D A3.A)).H) => (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : (R.toCx3 F).W i) ∈
      LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0)) hw' ?_ ?_ ?_
    · intro p x hx
      have hlam := hpos.2 i A3.A.μ0 p
      have ha : LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) =
          Tw.map (twAt D.what₂.embLL A3.A.v0) (LinearMap.adjoint (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) :=
        congrArg (fun f => f (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) (Formalism.IndefR.Links.Tw.adjoint_map (s := (twAt D.what₂.embLL A3.A.v0)) (R.thG i A3.A.μ0))
      have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) =
          ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) • Tw.mk (twAt D.what₂.embLL A3.A.v0) x := by
        refine (congrArg (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) ha).trans ?_
        show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0 (LinearMap.adjoint (R.thG i A3.A.μ0) x)) = _
        rw [hA i A3.A.μ0 p _ hx, Tw.mk_smul, cj_ofReal]
      have h3 := (Formalism.IndefR.Links.RealDat3.phase_cancel hcc (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)).trans key
      refine ⟨((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x), ?_⟩
      change (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) x
      refine (map_smul _ _ _).trans ((congrArg (fun z => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ • z) h3).trans ?_)
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam.ne'), one_smul]
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  unfold principalFormsSubspace
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨c, rfl⟩
    rw [(R.toCx3 F).tC_eq]
    exact hsub t _ ⟨_, rfl⟩
  · exact (hsup.trans (hrng A3.A.μ0)).trans
      (le_iSup (fun t => LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) A3.A.μ0)

end GlobalTheory.WgLift
