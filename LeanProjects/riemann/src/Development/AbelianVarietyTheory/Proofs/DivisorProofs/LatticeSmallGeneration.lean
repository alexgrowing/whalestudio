import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem coefLat_le_span {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hC : GlobalTheory.Hk3.Core R F) (hFW : Nonempty (FWTie T R κw v₀))
    (hio : IoExt R) (i : Fin D.R.m) (hO : OMPins T R κw v₀ O i) (B : Base (Vc D i) (Wc D i)) (hB : B.Good)
    (hBo : BaseOf R i B) {Oc Oc' : Subring ℂ} (hc : IsCoefRing (embLL0 D) (labLL0 D) Oc)
    (hc' : IsCoefRing (embLL0 D) (labLL0 D) Oc') (h : Bridge.Gf (Vc D i)) {P : PolF D (Wc D i).rank (Vc D i).rank}
    (hP : P ∈ B.coefLat (embLL0 D) (labLL0 D) Oc h) :
    P ∈ Submodule.span Oc (B.coefLat (embLL0 D) (labLL0 D) Oc' h : Set (PolF D (Wc D i).rank (Vc D i).rank)) := by
  obtain ⟨c, hcE, -, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κw v₀ hC hFW i Unit _ (O i) hO.2
  obtain ⟨u, w₀, hu, -, -⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  obtain ⟨κ, -, -, -, hL⟩ := GlobalTheory.CoefLatConj.coefLat_conj D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hcE u hu B hB hBo
  have e1 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc hc).1 h
  have e2 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc' hc').1 h
  rw [e1] at hP
  refine Submodule.span_mono ?_ hP
  intro Q hQ
  rw [SetLike.mem_coe, e2]
  exact Submodule.subset_span hQ

theorem baseOf_of_realPin_at {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem smallInt_isCoefRing (D : D7) : IsCoefRing (embLL0 D) (labLL0 D) (smallInt D) :=
  ⟨embLL0_labLL0, fun a => ⟨a, rfl⟩⟩

theorem latSmallGen : LatSmallGen := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p hR hM w _ j ρ hρ hpin h P hP => ?_⟩
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) :=
    by
      have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
      exact { h0 with }
  exact coefLat_le_span hC ⟨fw2 p⟩ hio j (hL.2.2.2.2.2.2.1 j) _ (hρ.base _ j _) hBo (hρ.isCoefRing _ _)
    (smallInt_isCoefRing _) _ hP

end GlobalTheory.BigOn.Exp
