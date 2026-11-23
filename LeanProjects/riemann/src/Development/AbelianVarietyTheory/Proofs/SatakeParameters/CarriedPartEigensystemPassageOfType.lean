import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftSplitHeckePolysEqTransferResidualPolysStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartnerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Fwd

theorem sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V)
    (op : I → Module.End K V) (opC : I → Module.End ℂ W)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (hint : ∀ i x, j (op i x) = opC i (j x)) (hc : Formalism.L2.Col.PairComm opC) (Q : (I → K) → Prop) {u : W}
    (hu : u ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V))) (hu0 : u ≠ 0) {y : I → ℂ}
    (hy : ∀ i, opC i u = y i • u) : ∃ s, Q s ∧ y = fun i => σ (s i) := by
  have h1 := (GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp hint).2.1 Q
  rw [h1] at hu
  by_contra hne
  have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ∃ s, Q s ∧ x = fun i => σ (s i)) (C' := fun x => x = y)
    (fun x hx h => hne (h ▸ hx))
  have hu' : u ∈ Formalism.L2.Col.eigSum opC (fun x => x = y) :=
    Formalism.L2.Col.eigAt_le_eigSum (op := opC) (C := fun x => x = y) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hy)
  exact hu0 ((Submodule.disjoint_def.1 hd) u hu hu')

end GlobalTheory.Hk3.Fwd

open GlobalTheory.Hk3.Fwd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.passage_of_carried : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos hB hTr j pl cV cW hLD p c hCar hW
  obtain ⟨sy, x, hxg, hxe, hxW, hx0, hlab⟩ :=
    GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part hHowe R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos j pl cV cW hLD p c hCar hW
  obtain ⟨hCore, hSF, -, -, hEE, hWW, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCar.1
  have hu0 := GlobalTheory.T.upward_theta_lift_injective_on_carried_part R F hB hPos p c hCar w hw hw0
  obtain ⟨hOpsX, hOpsV⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models
  obtain ⟨hX, hXo, hXn⟩ := hOpsX A3.A.μ0
  obtain ⟨hV, hVo, -⟩ := hOpsV j A3.A.μ0
  obtain ⟨plX, cX, c0, hRD⟩ := GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hHowe R F hInt hC hEx hSch hJ A3.A.μ0
  have hsplit := GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 core.lev core.fam core.models
  have hM := core.models
  have hBx := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R A3.A.μ0).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX A3.A.μ0
  have hk := kForm_semi (R.jX A3.A.μ0) (R.HX A3.A.μ0).e (R.B.R A3.A.μ0).pres.extL (fun x => hM.jX A3.A.μ0 x) hinj
    (hrange.trans hBx.2.symm) (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hBx.1
  have hjop : ∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = hX (plX i) (cX i) (R.jX A3.A.μ0 f) := hRD.op hX hXo
  have hcomm : Formalism.L2.Col.PairComm (fun i => hX (plX i) (cX i)) := fun a b => hXn.1 _ _ (hRD.good a) (hRD.good b) _ _
  have hwE : w ∈ EEc R.toRealDat R.SF c := hEE c ▸ hw
  have hy : ∀ i, hX (plX i) (cX i) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
      evC (Yc D 0) (plX i) (fun d => c (plX i) (dualLab d)) (c0 i) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 core hSch R.SF hSF A3.A.μ0 (plX i) (hRD.good i) (cX i) (c0 i) (hRD.mat i) hX hXo).2 c w hwE
  have hu : LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (R.jX A3.A.μ0 ''
      (Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll ((A3.rowI A3.A.μ0).HasRes3 p.1) : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hCar.2 (Submodule.mem_map_of_mem hw)
  obtain ⟨sR, hsR, hyR⟩ := sys_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (Module.Basis.ofVectorSpace _ _)
    (A3.rowI A3.A.μ0).opAll (fun i => hX (plX i) (cX i)) hk.1 hk.2 hjop hcomm _ hu hu0 hy
  have hXs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ D.sp.X'.rank →
      hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
        D.what₂.embLL (sR (Sum.inl (P, k))) • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P k hkr
    have heq : hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) = hX (plX (Sum.inl (P, k))) (cX (Sum.inl (P, k))) := by
      refine LinearMap.ext_on hk.2 ?_
      rintro _ ⟨b, rfl⟩
      exact ((hsplit.1 A3.A.μ0 hX hXo P k hkr _).symm).trans (hjop (Sum.inl (P, k)) _)
    exact (LinearMap.congr_fun heq _).trans ((hy (Sum.inl (P, k))).trans
      (congrArg (fun z : ℂ => z • LinearMap.adjoint (R.Th A3.A.μ0) w) (congrFun hyR (Sum.inl (P, k)))))
  have hVs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ (Vc D j).rank →
      hV (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (sy (Sum.inl (P, k))) • R.jV j A3.A.μ0 x := by
    intro P k hkr
    have h1 : A3.A.heckeL j A3.A.μ0 (P, k) x = sy (Sum.inl (P, k)) • x := hxe (Sum.inl (P, k))
    exact (hsplit.2 j A3.A.μ0 hV hVo P k hkr x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) h1).trans ((R.jV j A3.A.μ0).map_smulₛₗ _ x))
  have hL := GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys R.toRealDat F.lv2 hInt core hSch hOk.ok2.irr R.SF hSF j c p.1.1 (fun i => sR (Sum.inl i))
    (fun i => sy (Sum.inl i)) hsR.1 hX hV hXo hVo w hwE hu0 hXs (R.jV j A3.A.μ0 x) (hWW j c ▸ hxW) hx0 hVs
  exact ⟨sy, ⟨hL, hTr j p c hCar sy ⟨x, hxg, hxe, hxW, hx0⟩⟩, hlab⟩
