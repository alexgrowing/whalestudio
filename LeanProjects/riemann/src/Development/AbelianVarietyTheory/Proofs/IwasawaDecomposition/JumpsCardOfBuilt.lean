import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jumpsCard_of_built (hH : HtCard) {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} (b : NBuilt hL D')
    (fr : OmFrame b.D) (hp : PhtOn b.A.wd fr fun _ _ _ _ => True) : JumpsCard D'.nd D'.naut := by
  obtain ⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  intro i a r w τ hw hτ hdR
  have hdA := ((Au.wdOf i a r w).2.2.2.1).mp hdR
  have e1 := (Au.wdOf i a r w).2.2.2.2 τ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have e2 := hp.card _ (L.Y.naut.iotaQC i) a r τ w trivial (fun x => (hτ x).symm) hdA
  show Multiset.card (L.Y.jumpsW i r τ) = a
  rw [e1, e2]

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

theorem jumpsCard_atMem : HtCard → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro hH hL
  refine evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  obtain ⟨fr, -, hp⟩ := (e : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd).pht
  exact jumpsCard_of_built hH c.a.nt.toNBuilt fr hp

end GlobalTheory.HeightCounting.JumpsAt
