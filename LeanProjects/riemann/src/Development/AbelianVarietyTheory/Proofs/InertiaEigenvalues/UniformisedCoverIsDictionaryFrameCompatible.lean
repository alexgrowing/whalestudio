import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem relab_and_goodEmb_of_inc {D : D7} (T : CoreJ D) (j : ℕ) (C : Cover T j T.σ₀) (hinc : C.σ₂.comp C.inc = T.σ₀) :
    (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  have key : ∀ (z : ℂ) (hz : z ∈ T.Q.c.F) (hz2 : z ∈ C.d.c₂.F), C.σ₂ ⟨z, hz2⟩ = z := by
    intro z hz hz2
    have h1 : (⟨z, hz2⟩ : C.d.c₂.F) = C.inc ⟨z, hz⟩ := Subtype.ext rfl
    have h2 : C.σ₂ (C.inc ⟨z, hz⟩) = T.σ₀ ⟨z, hz⟩ := by rw [← RingHom.comp_apply, hinc]
    rw [h1, h2]
    rfl
  refine ⟨fun τ => RingHom.ext fun x => key _ (T.Q.c.conj τ x) _, ?_⟩
  have hz : T.Q.H.rt0 ∈ T.Q.c.F := GlobalTheory.coe_baseKA_rho T.Q.l ▸ T.Q.c.le (baseKA T.Q.l).ρ.2
  have hz2 : T.Q.H.rt0 ∈ C.d.c₂.F := GlobalTheory.coe_baseKA_rho C.d.l₂ ▸ C.d.c₂.le (baseKA C.d.l₂).ρ.2
  have e : (IntermediateField.inclusion C.d.c₂.le) (baseKA C.d.l₂).ρ = ⟨T.Q.H.rt0, hz2⟩ :=
    Subtype.ext (GlobalTheory.coe_baseKA_rho C.d.l₂)
  unfold GoodEmb
  rw [RingHom.comp_apply]
  erw [e]
  exact key _ hz hz2

theorem isDict_cover_of_isUnif {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (W : HSp D)
    (hV : T.V j T.σ₀ = W) (hr : W.rank = D.R.r) (C : Cover T j T.σ₀) (hC : C.IsUnif) (hGE : GoodEmb C.d.c₂ C.σ₂) :
    IsDict C.U₂ W hr (castDict hV C.dict₂) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j)
        (T.x₀ j T.σ₀) := by
  subst hV
  obtain ⟨-, -, -, hU, -, hr', g, e, F, ik, φ, th, hMW, hth, hDL⟩ := hC
  have hP := hL.pins
  have hg := T.toCore.good_σ₀
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hio := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj _ hg _ rfl hr
  refine ⟨hU, hio.1, fun k => ⟨hMW k, fun τ => ?_, ?_⟩, fun k τ hτ => ?_, g, e, F, ik, φ, th, hth, hDL⟩
  · rw [(hU.2.1 k).2 τ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : (C.U₂.X k).κ0 = 2 * (C.U₂.X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hGE) hU' hr1 w k).1
    rw [h1, (hMW k).2, mul_neg]
  · rw [(hMW k).1, (hU.2.1 k).1]
    exact hio.2 τ (((hU.2.1 k).2 τ).1 hτ)

set_option maxHeartbeats 1000000 in

theorem cover_dict_frameTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL _ _ _ hmod _ hT i _ hV C hC
  have hj := inR i
  have hinc : C.σ₂.comp C.inc = T.σ₀ := hC.2.2.1
  obtain ⟨hrel, hGE⟩ := relab_and_goodEmb_of_inc T _ C hinc
  have hD := isDict_cover_of_isUnif T hL _ hj _ hV (rank_Wc i) C hC hGE
  have hU := hD.1
  have hP := hL.pins
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hmod.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  refine ⟨hD, fun k => ⟨isInvOf_cart _ _ _ hx (by have := hU.1; have := (hU.2.1 k).1; omega) hε,
    fun hq => isBasOf_onb _ _ _ hx hq hε⟩, hrel, hGE⟩

end GlobalTheory.LevelSeries
