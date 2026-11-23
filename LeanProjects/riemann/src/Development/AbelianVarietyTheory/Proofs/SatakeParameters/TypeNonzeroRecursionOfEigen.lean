import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OntoPartAtOfZeroOrInjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeNZJoin

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie

set_option maxHeartbeats 1000000 in

theorem inj_at {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (hT : ∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) (i : D.nd.Loc) (hS : GlobalTheory.NJoin.EigString X i)
    (hG : GlobalTheory.NJoin.EigGood X i) (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1))
    (hf : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x)
    (h0 : D.what₂.thetaP (D.nd.mu i) (j.1 + 1) f = 0) : f = 0 := by
  have hC := X.given.core
  have hfm := (X.IL.jMt _ hμ j f).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).symm
      ⟨((X.IL.jMt _ hμ j f).1 : Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).apply_symm_apply _)
  have hthG : X.R.thG j (X.tupT (D.nd.mu i)) y = 0 := by
    have hM := GlobalTheory.ThetaLevelP.thF_mem_level X.R X.F hC.lev hC.models hC.thP X.R.hv0 false j (X.tupT (D.nd.mu i)) y
      (by rw [hyf]; exact hfm.2)
    obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 (D.nd.mu i) hμ j f
    have hw' : PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) ∘ₗ
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).embK j =
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).thC _ j (X.IL.jMt _ hμ j f) := by
      rw [← hy]; rfl
    have hwe : w = PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) := by
      refine sub_eq_zero.1 (X.fire.2.2 j _ (sub_mem hw1 (Submodule.mem_map_of_mem hM)) ?_)
      exact (LinearMap.sub_comp _ _ _).trans (by rw [hw2]; exact sub_eq_zero.2 hw'.symm)
    have hth := X.recR.tied.lift.theta (D.nd.mu i) hμ j f w (X.fire.1 _ hμ j) hw1 hw2 hw3
    rw [h0, map_zero, ZeroMemClass.coe_zero, hwe] at hth
    have h2 : PiTensorProduct.lift (postOn _ (X.R.eWf j (sg0 D X.A)) (X.R.thF j (X.tupT (D.nd.mu i)) y)) = 0 := by
      rw [GlobalTheory.ThetaFireLift.lift_postOn]; exact hth.symm
    have h3 : (X.R.HW j (sg0 D X.A)).e (X.R.thG j (X.tupT (D.nd.mu i)) y) = 0 := by
      rw [hC.thP.thG]; exact (LinearEquiv.map_eq_zero_iff _).1 h2
    exact (hC.models.HW j _).1 (h3.trans (map_zero _).symm)
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := GlobalTheory.LiftOntoCompare.exists_opsV hC.lev hC.models j (X.tupT (D.nd.mu i))
    obtain ⟨s, hs1, hs2⟩ := hS hμ j hj x hx f hf y hyf hne h hh
    exact hne (hT j _ h hh s hs1 y hs2 (hG hμ j hj x hx f hf y hyf) hthG)
  have h4 : X.IL.jMt _ hμ j f = 0 := by
    apply Subtype.ext
    show X.fn hμ j f = 0
    rw [← hyf, hy0, map_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 h4

theorem of_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (S : Submodule ℂ (D.what₂.Mt μ b))
    (H : ∀ f : D.what₂.Mt μ a, (h ▸ f : D.what₂.Mt μ b) ∈ S → D.what₂.thetaP μ a f = 0 → f = 0) :
    ∀ F ∈ S, D.what₂.thetaP μ b F = 0 → F = 0 := by
  subst h
  exact H

theorem typeNZRec_of_join : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact of_cast hj _ fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0

end GlobalTheory.TypeNZJoin
