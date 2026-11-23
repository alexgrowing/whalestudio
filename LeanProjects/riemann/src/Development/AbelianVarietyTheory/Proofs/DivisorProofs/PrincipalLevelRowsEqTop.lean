import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.PrincipalRows

theorem theta_adjoint_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hKR : X.KFormR) (hJR : X.JIsoR cv) (hRT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) (S : Submodule ℂ X.EE)
    (hZ : ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ S) (e : X.EE) : X.Θ t (LinearMap.adjoint (X.Θ t) e) ∈ S := by
  obtain ⟨N, ψ, hψ, hr⟩ := hRT
  have hspan : Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t)) :=
    Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (CxData.bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  have hsub : LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤ S.comap (X.Θ t) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  exact hsub ⟨e, rfl⟩

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

theorem mem_range_toF_full {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (Z : Submodule K B.S.Forms) (z : B.S.Forms) (hz : z ∈ Z)
    (hg : z ∈ B.goodF Xc) : z ∈ LinearMap.range (B.toF ⟨Xc, ⊥, 1⟩ Z) := by
  rw [GlobalTheory.OneForm.range_toF]
  refine ⟨hz, ?_⟩
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  rw [← hw, Formalism.L2.DIV.CSD.gaOp, GlobalTheory.OneForm.asAlg_eq_sum, LinearMap.sum_apply]
  rfl

theorem theta_base_forms_mem_principal_good_part {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) :
    ∀ z ∈ X.Z A3.A.fam.μ0, X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 z) ∈
      EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R A3.A.fam.μ0).ZHg A3.A.fam.X := hIB.1 A3.A.fam.μ0 hz
  obtain ⟨x, hx⟩ := mem_range_toF_full (A3.A.fam.R A3.A.fam.μ0) A3.A.fam.X (X.zs.Z A3.A.fam.μ0) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0 x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 y)) hx

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

set_option maxHeartbeats 1000000 in

theorem principal_level_rows_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hTop hPos hB hRT hIB
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT A3.A.fam.μ0
    (EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc))
    (theta_base_forms_mem_principal_good_part A3 (R.toCx3 F) hIB)

  have hpart : ∀ p, ∀ y ∈ R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro p y hy
    have hc : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p := by
      refine mul_pos hPos.1 (Finset.prod_pos fun j _ => ?_)
      unfold RealDat3.lamN
      split_ifs
      · exact hPos.2 _ _ _
      · exact one_pos
    have hne : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hce : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y ∈ R.EEp3 p :=
      (R.EEp3 p).smul_mem _ hy
    have key : R.Th A3.A.fam.μ0 (LinearMap.adjoint (R.Th A3.A.fam.μ0)
        (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y)) = y := by
      refine (hB A3.A.fam.μ0 p _ hce).trans ?_
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 := hmem (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))
    have h4 : (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)
        (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) y := by
      show Tw.map _ (R.Th A3.A.fam.μ0) (LinearMap.adjoint (Tw.map _ (R.Th A3.A.fam.μ0)) _) = _
      rw [Tw.adjoint_map]
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) key
    rw [h4] at h3
    exact h3
  rw [eq_top_iff]
  intro e0 _
  have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e0 ∈ ⨆ p, R.EEp3 p := by rw [hTop]; exact Submodule.mem_top
  have hall : ∀ y ∈ ⨆ p, R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro y hy
    exact Submodule.iSup_induction R.EEp3 (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) hy hpart
      (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
  exact hall _ hx

end GlobalTheory.PrincipalRows
