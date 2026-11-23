import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSideV
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 N : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
  {j : Fin D.R.m} {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X)

set_option maxHeartbeats 2000000 in

theorem baseOf_ext {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (extR R Y) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

set_option maxHeartbeats 2000000 in

theorem ext_ext : Ext T R κ v₀ O j (extR R Y) v₀ (fun i => omExt Y (O i)) := by
  refine ⟨fun τ h => (fixBase_ext Y j τ).2 h, fun τ ζ Φ Φ' h => ?_, ?_⟩
  · exact (h)
  · exact (by with_unfolding_all exact ((Ext.refl (T := T) (R := R) (κ := κ) (v₀ := v₀) (O := O) (j := j)).2.2 :))

end

set_option maxHeartbeats 2000000 in

theorem extend_tuples : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  intro h1 _ _ h4 h5 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL N _ χ xi Q xiR hV hi hn hQ
  obt ⟨hC, hfin, ⟨hfw⟩, hio, hg, hp, hph, hB⟩ := hL
  let V : NewLev D N := ⟨χ, xi, Q, xiR⟩
  have hL' : (extL R.toLevCh V).Is (.inl A.μ0) := extL_is hC.lev hV hi hn hQ
  obt ⟨X, Y0, h0⟩ := fam_stage (GlobalTheory.SideLevel.sideReal_moreLevel) hC hL' hV
  obt ⟨Y, hC', hT⟩ := core_ext h4 GlobalTheory.HcPort.print_harishChandraModules h1 h5 (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hC hL' Y0 h0
  have hg' : QGuard (extR R Y) := ⟨Sum.rec hg.1 fun n => (hV n).half, Sum.rec hg.2 fun n => (hV n).guard⟩
  exact ⟨T0 ⊕ N, extA A X, extR R Y, extF F X, v₀, fun i => omExt Y (O i),
    ⟨hC', inferInstance, ⟨fwExt Y hfw⟩, ioExt_ext R Y hio, hg', omPins_ext Y hT hp, phaseTie_ext Y hph, baseOf_ext Y hB⟩,
    ext_ext Y, fun n => ⟨.inr n, rfl, rfl⟩⟩

end GlobalTheory.TupExt

end
