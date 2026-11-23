import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHeckeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupStableInfTypeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankISupEqOfISupIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

section Tw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool)

theorem twSub_map (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem twSub_iSup {C : Type} (S : C → Prop) (V : C → Submodule ℂ E) :
    Tw.sub s (⨆ (c : C) (_ : S c), V c) = ⨆ (c : C) (_ : S c), Tw.sub s (V c) := by
  rw [← twSub_map, Submodule.map_iSup]
  refine iSup_congr fun c => ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ => ?_
  exact twSub_map s (V c)

theorem twSub_finrank (V : Submodule ℂ E) : Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  unfold Module.finrank
  congr 1
  symm
  exact rank_eq_of_equiv_equiv (cj s)
    (show V ≃+ Tw.sub s V from
      { toFun := fun x => ⟨Tw.mk s x.1, x.2⟩
        invFun := fun x => ⟨Tw.out x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
    (Function.Involutive.bijective (cj_cj s))
    (fun r m => Subtype.ext ((Tw.mkL s E).map_smulₛₗ r m.1))

theorem twSub_le {V V' : Submodule ℂ E} (h : V ≤ V') : Tw.sub s V ≤ Tw.sub s V' := fun _ hx => h hx

theorem twSub_stable {G : Type} [Group G] (ρ : Representation ℂ G E) (V : Submodule ℂ E)
    (h : ∀ g, V.map (ρ g) ≤ V) (g : G) : (Tw.sub s V).map (Tw.rep s ρ g) ≤ Tw.sub s V := by
  rintro _ ⟨x, hx, rfl⟩
  exact h g ⟨Tw.out x, hx, rfl⟩

end Tw

theorem twSub_iSup_inf_level {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {G : Type} [Group G] [Fintype G]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) {C : Type} (S : C → Prop) (U : C → Submodule ℂ E)
    (B Lev : Submodule ℂ E) (hUB : ∀ c, U c ≤ B) (hstab : ∀ c g, (U c).map (ρ g) ≤ U c)
    (hLev : Tw.sub s Lev = Tw.sub s B ⊓
      ⨅ h : P, LinearMap.ker (Tw.rep s ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) :
    Tw.sub s (⨆ (c : C) (_ : S c), U c) ⊓ Tw.sub s Lev = Tw.sub s (⨆ (c : C) (_ : S c), U c ⊓ Lev) := by
  rw [twSub_iSup, hLev, ← inf_assoc, inf_eq_left.2 (iSup₂_le fun c _ => twSub_le s (hUB c)),
    GlobalTheory.iSup_stable_inf_typeSpace (Tw.rep s ρ) P ψ _ S (fun c g => twSub_stable s ρ _ (hstab c) g), twSub_iSup]
  refine iSup_congr fun c => iSup_congr fun _ => ?_
  show _ = Tw.sub s (U c) ⊓ Tw.sub s Lev
  rw [hLev, ← inf_assoc, inf_eq_left.2 (twSub_le s (hUB c))]

open Classical in
theorem evC_single {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) :
    GlobalTheory.Hk3.evC V P a (Finsupp.single d 1) = if IsLab V P d then a d else 0 := by
  unfold GlobalTheory.Hk3.evC
  rw [Finsupp.sum_single_index]
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem dimParts_of_schur {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hX : GoodStable A3.A.X) (hD : GlobalTheory.CuspMult.CuspDecomp D) (hM : GlobalTheory.CuspMult.MultEq R.toRealDat)
    (hU : R.toRealDat.LUnif) (hS : SchurAll R.toRealDat) : (R.toCx3 F).DimParts false := by
  obtain ⟨hC, hSF, hEE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE, -, -, -, hEev, hEchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  intro j p
  obtain ⟨hWo, -, -, -, hWtop, hWstab, hWev, hWchar⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hC hS hIrr R.SF hSF j
  have hI := (GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hC hIrr j).1
  have hlab : ∀ P d, Good R.toRealDat A3.A.μ0 P → (IsLab (Wc D j) P d ↔ IsLab (Yc D 0) P (dualLab d)) :=
    fun P d hP => (GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := 0) R.toRealDat F.lv2 hC j P d hP).1
  let LevW : Submodule ℂ (R.HW j (sg0 D A3.A)).H :=
    (R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW j (sg0 D A3.A)).e
  let LevE : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e
  have hWle : ∀ c, Wcc R.toRealDat R.SF j c ≤ LinearMap.range (eH R.toRealDat j) := fun c =>
    hWtop ▸ le_iSup (fun c => Wcc R.toRealDat R.SF j c) c
  have hr1 : LinearMap.range ((R.toCx3 F).w0C false j) = Tw.sub (twAt D.what₂.embLL A3.A.v0) LevW :=
    GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false j
  have hr2 := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  have hWside : (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c ⊓ LevW) := by
    have e0 : (R.toCx3 F).Wp j p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c) := by
      show Tw.sub _ (R.Wp3 j p) = _
      unfold RealDat3.Wp3
      simp only [hWc]
    rw [e0, hr1]
    exact twSub_iSup_inf_level _ (R.gW j (sg0 D A3.A)) F.P0 ((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0⁻¹)
      (R.Carries p) _ _ LevW hWle hWstab (hr1.symm.trans hr2)
  have hEside : (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c ⊓ LevE) := by
    have e0 : (R.toCx3 F).EEp p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c) := by
      show Tw.sub _ (R.EEp3 p) = _
      unfold RealDat3.EEp3
      simp only [hEE]
    have hl : Tw.sub (twAt D.what₂.embLL A3.A.v0) LevE = Tw.sub (twAt D.what₂.embLL A3.A.v0) ⊤ ⊓
        ⨅ h : F.P0, LinearMap.ker (Tw.rep (twAt D.what₂.embLL A3.A.v0) R.gE (h : G) -
          ((((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0) h : ℂˣ) : ℂ) • LinearMap.id) := by
      have := (GlobalTheory.T.level_rows_eq_type_vectors_of_level R F hW).1
      refine this.trans ?_
      ext x
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [e0]
    exact twSub_iSup_inf_level _ R.gE F.P0 _ (R.Carries p) _ ⊤ LevE (fun _ => le_top)
      (fun c g => GlobalTheory.T.rowParts_full_spherical_algebra_stable_finiteGroup (s := 0) R.toRealDat F.lv2 hC R.SF hSF c g) hl
  rw [hWside, hEside]
  refine (twSub_finrank (E := (R.HW j (sg0 D A3.A)).H) _ _).trans (Eq.trans ?_ (twSub_finrank (E := R.HE.H) _ _).symm)
  have hWfix : ∀ c, ∀ x ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j x = x := by
    intro c x hx
    obtain ⟨y, rfl⟩ := hWle c hx
    rw [← Module.End.mul_apply, hI]
  let I := {x : Pl D.host.E × List ℤ // Good R.toRealDat A3.A.μ0 x.1 ∧ IsLab (Wc D j) x.1 x.2}
  let lab : (Pl D.host.E → List ℤ → ℂ) → I → ℂ := fun c i => c i.1.1 i.1.2
  have hEle : ∀ c c', lab c = lab c' → EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
    intro c c' hcc x hx
    refine hEchar c' x fun P d hP hd => ?_
    rw [hEev c P hP _ x hx, evC_single, if_pos hd]
    have hl : IsLab (Wc D j) P (dualLab d) := (hlab P (dualLab d) hP).2 (by rwa [dualLab_dualLab'])
    exact congrArg (· • x) (congrFun hcc ⟨(P, dualLab d), hP, hl⟩)
  have hWcle : ∀ c c', lab c = lab c' → Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro c c' hcc x hx
    refine hWchar c' x (hWfix c x hx) fun P d hP hd => ?_
    rw [hWev c P hP _ x hx, evC_single, if_pos hd]
    exact congrArg (· • x) (congrFun hcc ⟨(P, d), hP, hd⟩)
  symm
  refine GlobalTheory.finrank_iSup_joint_eigen_eq (I := I)
    (fun i => hE i.1.1 (Finsupp.single (dualLab i.1.2) 1)) (fun i => hWo i.1.1 (Finsupp.single i.1.2 1))
    (fun c => EEc R.toRealDat R.SF c ⊓ LevE) (fun c => Wcc R.toRealDat R.SF j c ⊓ LevW) lab ?_ ?_ ?_ ?_ (R.Carries p)
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hEev c P hP _ x hx.1, evC_single, if_pos ((hlab P d hP).1 hd), dualLab_dualLab']
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hWev c P hP _ x hx.1, evC_single, if_pos hd]
  · intro c c' hcc
    rw [le_antisymm (hEle c c' hcc) (hEle c' c hcc.symm), le_antisymm (hWcle c c' hcc) (hWcle c' c hcc.symm)]
    exact ⟨rfl, rfl⟩
  · intro c
    exact (GlobalTheory.T.finrank_W_eigenpart_eq_rows_full_hecke R.toRealDat F.lv2 hOk.ok2 hC hS hX hD hM R.SF hSF F.P0 F.ψ0 j c).symm

end GlobalTheory.DimPartsFull

end
