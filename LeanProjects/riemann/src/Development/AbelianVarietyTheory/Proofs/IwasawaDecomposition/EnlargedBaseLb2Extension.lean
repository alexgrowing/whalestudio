import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyGrid
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ListCarry
open GlobalTheory.Mem.R3.Tr GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.TwInputs.Move

open Classical in

def movePl {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L)
    (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (v : HeightOneSpectrum (𝓞 D.host.F))
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hv : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (hS : v ∉ S1 D)
    (hu : u.under (𝓞 D.host.F) = v) (hs : ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e u) : Places L where
  v0 := v
  basePlace_over_qZero := hv
  w := Function.update P.w v u
  w_over x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hu
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_over x (Finset.mem_insert_of_mem hx)
  w_split x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_split x (Finset.mem_insert_of_mem hx)
  w_g x k hx := by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      fin_cases k
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact P.w_g x k hx
  w_de p hp := (P.w_de p hp).imp fun 𝔭 h x hx => by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      rcases hp with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx)))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact h x hx
  w_Q t PP hP h := by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem h hS)]
    exact P.w_Q t PP hP h
  levelPlace_ne_basePlace t PP hP e := by
    subst e
    refine h4 t PP hP ?_
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((q0 D : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hv
    rwa [map_natCast] at this

theorem movePl_w {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L) (h4 v u hv hS hu hs) :
    (movePl P h4 v u hv hS hu hs).w v = u := by
  simp only [movePl, Function.update_self]

theorem listPin_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    (hj : HEq D.ntw.jL D'.ntw.jL) (hs : HEq D.ntw.s2 D'.ntw.s2) (hX : HEq D.ntw.Xv D'.ntw.Xv) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D' ≠ D'.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D' : ℕ) : 𝓞 D'.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D' Lc' CF b := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h.gal
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.set
  have b1 := h.sp
  have b2 := h.Tau
  have b3 := h.instTau
  have b4 := h.eTau
  have b5 := h.hc
  cases D'
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst a1; subst a2; subst a3; subst b1
  rename Rows.Data _ => rows'
  cases rows'
  dsimp only at b2 b3 b4 b5
  subst b2; subst b3; subst b4; subst b5
  rename NData _ _ _ => N'
  cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => X'
  cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hj; subst hs; subst hX
  obtain ⟨G, hF, hT⟩ := hp
  have hmu := eq_of_heq hmu
  have hd := eq_of_heq hd
  have hd' := eq_of_heq hd'
  have h0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  obtain ⟨P₀⟩ := hP fun k e => h0 ((S1_mem_OmF D).2 (by
    have e' : q0 D = D.host.g k := e
    have := G.pl.basePlace_over_qZero
    rw [e'] at this
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  have hm : G.pl.v0 ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)
  let P : Places Lc' := movePl P₀ h4 G.pl.v0 (G.pl.w G.pl.v0) G.pl.basePlace_over_qZero h0 (G.pl.under_w hm) ((G.pl.w_split G.pl.v0 hm))
  have hw : P.w P.v0 = G.pl.w G.pl.v0 := movePl_w ..
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA _).2 I' Lc' P ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices _ I' Lc' _ _ (GlobalTheory.ChiGrid.colY_isV _ I' Lc' μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  let X : Chars P 1 := ⟨G.ch.chiH, (G.ch.chi), (G.ch.chi_eq), (G.ch.triv), (G.ch.inf), (G.ch.unr),
    (G.ch.lev1), (G.ch.wild), (G.ch.lev0)⟩
  refine ⟨⟨P, X, V⟩, ⟨fun i a c v hv => ?_, fun v hv => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨y, hy⟩ := hF.values i a c v hv
    exact ⟨e.symm y, by rw [← h.embLL0_eq, e.apply_symm_apply]; exact hy⟩
  · obtain ⟨z, hz⟩ := hF.roots v hv
    exact ⟨e.symm z, hz.map_of_injective (f := e.symm) e.symm.injective⟩
  · obtain ⟨t0, j, t1, t2⟩ := hT i ((h.inW1 i i HEq.rfl).2 hi)
    have hl : ∀ l a c, (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).lam0 l a c = (lamOf G).lam0 l a c := fun l a c => by
      change Lc'.C.mu0 a * (if l = D.host.pde then Lc'.C.del' else Lc'.C.del) * _ = _
      rw [hmu, hd, hd']
      rfl
    have hw' : (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).w0 = (lamOf G).w0 := hw
    refine ⟨by rw [hw']; exact t0, j, fun x => ?_, ?_⟩
    · exact (congrArg j (h.embLL0_eq x).symm).trans ((t1 (e x)).trans (congrArg _ (eq_of_heq (h.emb0 i i HEq.rfl x))))
    · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, hw']
      exact t2

theorem twistPlaces_not_over_leastSplitAuxiliaryPrime {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) : ∀ t, ∀ PP ∈ z.R.toRealDat.toLevCh.Q t,
      ((q0 (w.st Z).toD7 : ℕ) : 𝓞 (w.st Z).toD7.host.E) ∉ PP.asIdeal := by
  intro t PP hP hq
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

theorem fr_heq {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f'.mu0 f.mu0 ∧ HEq f'.del f.del ∧ HEq f'.del' f.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem lev_fr {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    HEq x.m.z.R.toRealDat.toLevCh.C.mu0 f.mu0 ∧ HEq x.m.z.R.toRealDat.toLevCh.C.del f.del ∧
      HEq x.m.z.R.toRealDat.toLevCh.C.del' f.del' := by
  rw [(GlobalTheory.HeightCounting.Up.ListModel.lev_at_state x).1]
  obtain ⟨h1, h2, h3⟩ := fr_heq rfl (heq_of_eq w.C_eq)
  exact ⟨(h1), (h2), (h3)⟩

theorem listPin_copyN {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e)
    {D'' : D7} (hD : D'' = N.toD7) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D'' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D'' ≠ D''.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D'' : ℕ) : 𝓞 D''.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D'' Lc' CF b := by
  subst hD
  exact listPin_copy h.cp h.jL h.s2 h.Xv hL hmu hd hd' hP h4 hp

theorem listSt_carry : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : LI hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  intro _ _ hL K B' f' T' w' _ _ _ B f T w hE hf _ _ _ _ _ P x _ P' _ x' _ _ N ι e hc x'' _ ho _ _ _ _ _ _ _ _ cDep hp
  have hD : Dof x'' = N.toD7 := by
    unfold Dof
    rw [ho]
    exact dof_oTw x' N
  obtain ⟨a1, a2, a3⟩ := lev_fr x
  obtain ⟨b1, b2, b3⟩ := lev_fr x''
  obtain ⟨c1, c2, c3⟩ := fr_heq hE.1 hf
  exact listPin_copyN hc hD x''.m.z.lev.is (b1.trans (c1.trans a1.symm)) (b2.trans (c2.trans a2.symm))
    (b3.trans (c3.trans a3.symm))
    (fun h3 => (GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w' x''.o.Z x''.m.z ⟨1, cDep, K.s.b⟩ h3).map fun G => G.pl)
    (twistPlaces_not_over_leastSplitAuxiliaryPrime w' x''.o.Z x''.m.z) hp

end GlobalTheory.HeightCounting.Up.ListCarry

end
