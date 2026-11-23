import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistOfGrid

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ListModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem listPin_anti {D : D7} {I : Type} {Lc : LevCh D I} {μ0 : I} (hL : Lc.Is μ0) {CF CF' b : ℝ} (h : CF ≤ CF') (hb : 1 ≤ b)
    (hp : ListPin D Lc CF' b) : ListPin D Lc CF b := GridModel.gridPin_anti hL h hb hp

theorem not_listPin {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) (h : q0 D = D.host.g 0) : ¬ ListPin D Lc CF b :=
  GridModel.not_gridPin Lc CF b h

theorem not_listPin_of_empty {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (h : IsEmpty (D.ntw.abelian₂ i)) : ¬ ListPin D Lc CF b := GridModel.not_gridPin_of_empty Lc CF b hi h

theorem listPin_transfer {D : D7} {I I' : Type} {Lc : LevCh D I} {Lc' : LevCh D I'} {μ0 : I'} (hL : Lc'.Is μ0) (hC : Lc'.C = Lc.C)
    {CF b : ℝ} (G : GridData Lc ⟨1, CF, b⟩) (hF : FieldHas G (embLL0 D)) (hT : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (P : Places Lc') (hv : P.v0 = G.pl.v0) : ListPin D Lc' CF b := by
  have hS : P.S0 = G.pl.S0 := by unfold Places.S0; rw [hv]
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 I' Lc' P ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices D I' Lc' _ _ (GlobalTheory.ChiGrid.colY_isV D I' Lc' μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  let X : Chars P 1 := ⟨G.ch.chiH, G.ch.chi, G.ch.chi_eq, G.ch.triv, G.ch.inf, fun i a b PP h => G.ch.unr i a b PP (hS ▸ h),
    G.ch.lev1, G.ch.wild, fun i a b PP h => G.ch.lev0 i a b PP (hv ▸ h)⟩
  have hc : GlobalTheory.LamTie.cond0 D.host (P.w P.v0) = GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0) := by
    have e : (P.w P.v0).under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
      rw [P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl)), G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), hv]
    exact congrArg (fun v : HeightOneSpectrum (𝓞 D.host.F) =>
      Ideal.span {((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' : ℕ) : 𝓞 D.host.F)} ^ 2 * v.asIdeal) e
  refine ⟨⟨P, X, V⟩, ⟨hF.values, fun v hv' => ?_⟩, ?_⟩
  · have := hF.roots v (hS ▸ hv')
    have e : P.depth ⟨1, CF, b⟩ v = G.pl.depth ⟨1, CF, b⟩ v := by unfold Places.depth; rw [hv]
    exact e ▸ this
  · intro i hi
    have := hT i hi
    simp only [GlobalTheory.LamTie.IsLam, GlobalTheory.LamTie.LamDat.lam0, GlobalTheory.LamTie.LamDat.kap, lamOf] at this ⊢
    rw [hc, hC]
    exact this

theorem listPin_iff_of_untwisted {D : D7} {I : Type} (Lc : LevCh D I) (CF b : ℝ) (h : ∀ i, ¬ D.ntw.NonzeroIndexPlace i) :
    ListPin D Lc CF b ↔ ∃ G : GridData Lc ⟨1, CF, b⟩, FieldHas G (embLL0 D) :=
  ⟨fun ⟨G, a, _⟩ => ⟨G, a⟩, fun ⟨G, a⟩ => ⟨G, a, fun i hi => (h i hi).elim⟩⟩

section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem listPin_of_fit (p : PtAt ex Csz) {CF : ℝ} {G : Grid p CF} (h : GridFit p G) : ListPin D p.R.toRealDat.toLevCh CF L.sc.b :=
  ⟨G, h.field, h.list⟩

theorem fit_of_listPin (p : PtAt ex Csz) {CF : ℝ} (hp : ListPin D p.R.toRealDat.toLevCh CF L.sc.b) {xd v0 rep}
    (ht : GlobalTheory.EX.TwistAt L ex.nch xd v0 rep) (h1 : ValLL0 D p.R.C) (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) :
    ∃ G : Grid p CF, GridFit p G :=
  let ⟨G, a, b⟩ := hp
  ⟨G, GridFit.of_twistAt ht h1 a h3 b⟩

end Guard

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem settingsFormsExist_of_grid : SettingsFormsExistList hL cDep → SettingsFormsExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem seriesExist_of_grid : SeriesExistList hL cDep → SeriesExist hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting in

theorem moduliPointsExist_of_grid : ModuliPointsExistList hL cDep → SB2 hL := fun h =>
  Step.trans h (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => (H w a P x l).imp fun _ t => t.1)

open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.R3.Rw in

theorem chain (h0 : SettingsFormsExistList hL cDep) (h1 : SeriesExistList hL cDep) (h2 : ModuliPointsExistList hL cDep) (h3 : SC hL) :
    AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (LC hL x') ∧ ListSt cDep x' :=
  Step.trans (Step.and h0 (Step.and h1 (Step.and h2 h3))) (Step.of_all fun _ _ _ _ _ _ _ H w a P x l => by
    obtain ⟨x0, ⟨l0⟩, p0⟩ := H.1 w a P x l
    obtain ⟨x1, ⟨l1⟩, p1⟩ := H.2.1 w a P x0 l0
    obtain ⟨x2, ⟨l2⟩, p2⟩ := H.2.2.1 w a P x1 l1
    obtain ⟨c⟩ := H.2.2.2 w a P x2 l2
    exact ⟨x2, ⟨⟨l2, c⟩⟩, p2 (p1 p0)⟩)

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw in

theorem lev_at_state {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    x.m.z.R.toRealDat.toLevCh.C = cfOf x ∧ ∃ μ0, x.m.z.R.toRealDat.toLevCh.Is μ0 :=
  ⟨x.m.z.lev.C, _, x.m.z.lev.is⟩

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 in

theorem nonempty_grid {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (sc : Consts) (h3 : ∀ k, q0 (w.st Z).toD7 ≠ B.host.g k) :
    Nonempty (GridData z.R.toRealDat.toLevCh sc) := by
  refine GlobalTheory.ChiGridModel.nonempty_gridData _ _ z.lev.is sc B.g_cond B.pde_cond.1 B.pde_cond.2 h3 fun t PP hP hq => ?_
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

end GlobalTheory.HeightCounting.Up.ListModel

end
