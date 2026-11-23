import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefThetaRead

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
  Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.ThetaTri GlobalTheory.ThetaRead
open scoped TensorProduct InnerProductSpace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem fire (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    ThetaFireRow (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj) Y.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.lev core.grp core.models
      core.thP R.toRealDat.hv0 Y.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.models.inf⟩

set_option maxHeartbeats 1000000 in

theorem ipM_theta (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2)
    (hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T' T'' : MMap (R.MW j (sg0 D A3.A))) (hT : PiTensorProduct.lift T' = (Y.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T'' = (Y.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) T' T'' =
      ∫ g in R.fdW j, star (PiTensorProduct.lift T' (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g) *
        (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
          (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ)))
        ∂(R.νW j) := by
  have hM := core.models
  have hF := fire Y core
  obtain ⟨w, hw1, hw2, hw3⟩ := hF.2.1 μ hμ j x
  have hth := Y.tied.lift.theta μ hμ j x w (hF.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (Y.IL.jMj j y).2
  have hTT : T₀ = T' := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T'' = postOn (R.MW j (sg0 D A3.A)) (R.eWf j (sg0 D A3.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (R.MW j (sg0 D A3.A)) _ U).symm
  have hin : ∀ g, (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
      (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g := by
    intro g
    have e1 := (hF.1 _ hμ j).eq (Y.IL.jMt μ hμ j x) (kUnit (R.MW j (sg0 D A3.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj R.toRealDat hM hX j (mult_le_wall R.toRealDat F.lv2 false j hT1)
    (mult_le_wall R.toRealDat F.lv2 false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (R.MW j (sg0 D A3.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := hF.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (R.MW j (sg0 D A3.A)) _ _ _ _ hU0 _

set_option maxHeartbeats 1000000 in

theorem fV_eq (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) {M : MtFam D}
    (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hFm : (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) :
    GlobalTheory.RefTheta.fV Ad i Fm = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := by
  have e : (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) =
      fun k => (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ((Ad.PV i).ψ (preF (Ad.PV i) k)) := by
    funext k
    rw [hFm]
    exact Ad.read _ _ i x _
  change (R.cV i).ext (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) = _
  rw [e]
  obtain ⟨z, hz⟩ : (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ∈
      LinearMap.range (R.extV i (Y.tupT D.what₂.mu0)) := (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).2.1
  have hz' : (R.cV i).ext ((R.HV i (Y.tupT D.what₂.mu0)).e z) = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := hz
  generalize (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (core.models.cV i).1 _ _

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hFm
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have hf := fV_eq Y core Ad i x Fm hFm
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  have key : inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = (GlobalTheory.RefTheta.cC hc : ℂ) *
      ∫ g in R.fdW i, star (GlobalTheory.RefTheta.yv hc ⟨X.φ y, X.φ_mem y⟩ g) *
        (∫ h in R.fdV i (Y.tupT D.what₂.mu0), thetaKO (R.ωP i (Y.tupT D.what₂.mu0)) h g
          (GlobalTheory.RefTheta.phi0 Y i ((Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 h))
            ∂(R.νV i (Y.tupT D.what₂.mu0))) ∂(R.νW i) := by
    refine (X.φ_inner _ _).trans ((hB _ (X.φ_mem _) _ (X.φ_mem _)).trans (congrArg (fun z => (GlobalTheory.RefTheta.cC hc : ℂ) * z) ?_))
    exact ipM_theta Y core hX (GlobalTheory.RefTheta.reference_tuple_used D) i x y _ _ (hφ y) (hφ _)
  rw [key, ← hf]
  rfl

end GlobalTheory.RefThetaRead

end
