import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
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
  first | exact @GlobalTheory.TupExt.extend_tuples | exact GlobalTheory.TupExt.extend_tuples | (intros; apply GlobalTheory.TupExt.extend_tuples <;> assumption)
