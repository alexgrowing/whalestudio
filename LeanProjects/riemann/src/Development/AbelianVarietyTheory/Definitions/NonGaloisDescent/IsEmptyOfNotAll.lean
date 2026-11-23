import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr

noncomputable section
namespace GlobalTheory.TwInputs.JoinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section General

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}

def self (X : RealSide D) (Y : SerSide X (twEOf xd)) (g : GalSide D) (h1 : g.cf = X.R.C) (h2 : g.lam.C = X.R.C) (hF : FieldOk X)
    (cg : CGTrue hL D g.wd) (hb : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) :
    TwJoin hL D nch xd first X.R X.F X.cG X.geo Y.S Y.YS X.R.C :=
  ⟨X, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, Y, rfl, HEq.rfl, g, h1, h2, rfl,
    hF, cg, hb⟩

variable {G : Type} [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw}
  {YS : NExpRealS R cG S} {cf : CharFrame D}

def ofAt {H : NExpRealH R cG S YS} (a : TwAt hL D nch xd first R F cG geo S YS H cf) : TwJoin hL D nch xd first R F cG geo S YS cf :=
  ⟨a.X, a.Γ_eq, a.grp_eq, a.fin_eq, a.Pl0_eq, a.I0_eq, a.T_eq, a.core_eq, a.alg_eq, a.R_eq, a.F_eq, a.cG_eq, a.geo_eq, a.A3_eq, a.Y,
    a.S_eq, a.YS_eq, a.gal, a.cf_eq, a.lam_eq, a.C_eq, a.field, a.cg, a.base⟩

theorem elim (a : TwJoin hL D nch xd first R F cG geo S YS cf) :
    R.Char3 F ∧ R.C = cf ∧ GlobalTheory.RealGeo.InGeo geo ∧ Formalism.L2.Host.ValLL0 D cf ∧ XdAll xd ∧
      (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) ∧
      (∃ H : NExpRealH R cG S YS, GlobalTheory.ExportPin.Reads R cG S YS H.hL) ∧ Nonempty (ExportTie YS geo.v₀) ∧
      (∀ g : G, cG (R.eG g) ∈ D.nexp.U ↔ g ∈ F.P0) ∧ 100 ≤ D.R.r := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7, h8, hR, hF, hc, hg, hA, Y, hS, hY, g, -, -, hC, hf, -, -⟩ := a
  cases X
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hR hA hF hc hg hC
  subst h1 h4 h5 h6 h7
  cases h2; cases h3; cases h8; cases hA; cases hR; cases hF; cases hc; cases hg
  cases Y
  dsimp only at hS hY
  subst hS
  cases hY
  subst hC
  rename_i ch _ _ _ _ _ _ ig _ _ _ _ _ _ sup H rd _ Z U _ _ _ _ _ _ _ all
  exact ⟨ch, rfl, ig, hf.vals, fun i j b h1 h2 => Set.eq_univ_of_forall (all i j (Finset.mem_Icc.2 ⟨h1, h2⟩) b), sup, ⟨H, rd⟩, ⟨Z⟩, U,
    g.rank⟩

theorem isEmpty_of_not_all (h : ¬ XdAll xd) : IsEmpty (TwJoin hL D nch xd first R F cG geo S YS cf) :=
  ⟨fun a => h (elim a).2.2.2.2.1⟩

theorem isEmpty_of_ne (h : R.C ≠ cf) : IsEmpty (TwJoin hL D nch xd first R F cG geo S YS cf) :=
  ⟨fun a => h (elim a).2.1⟩

theorem psi_of_grp (h : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) (Z : ExportTie YS geo.v₀) (i b) (g : F.P0)
    (hg : cG (R.eG g) ∈ D.nexp.U) :
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, hg⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (F.ψ0 g : D.what₂.LLˣ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := h.psi0 g hg i b
  have h1 := Z.good.e_LL0 i b x
  refine (congrArg (Z.ρ.e i b) e).trans (h1.trans ?_)
  change D.what₂.embLL (x : D.what₂.LL) = _
  rw [hx, Units.val_inv_eq_inv_val, map_inv₀]

theorem low_of_tied {Fr : TwFrame D} (h : NTwTied D Fr) (hq : D.host.q ∣ (NumberField.discr D.host.E).natAbs) (i) (P : PlE D.host)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
      𝓞 D.host.E) ∈ P.asIdeal) : P ∈ D.ntw.S0 i := by
  have hp := P.isPrime
  have mem : ∀ p : ℕ, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i) → ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i :=
    fun p a b => a b
  have key : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    intro m
    induction m using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h1)) hp.ne_top
    | prime p pp => exact fun _ h1 => ⟨p, pp, dvd_rfl, h1⟩
    | mul a b iha ihb =>
      intro h0 h1
      rw [Nat.cast_mul] at h1
      rcases hp.mem_or_mem h1 with h1 | h1
      · obtain ⟨p, p1, p2, p3⟩ := iha (left_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_right _, p3⟩
      · obtain ⟨p, p1, p2, p3⟩ := ihb (right_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_left _, p3⟩
  simp only [Nat.cast_mul] at hP
  rcases hp.mem_or_mem hP with hP | hP
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · obtain ⟨p, p1, p2, p3⟩ := key _ D.host.QS_pos.ne' hP
        exact mem p ((h.two_ramified_places_subset_S0 i).2 p p1 ((D.host.dvd_natAbs_discr_iff p1).2 (p2.trans D.host.QS_dvd_condN))) p3
      · exact mem _ ((h.two_ramified_places_subset_S0 i).2 _ D.host.hyp.1 hq) hP
    · have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      obtain ⟨p, p1, p2, p3⟩ := key _ hN hP
      exact mem p (h.norm_ccK_places_subset_S0 i p p1 p2) p3
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · rcases hp.mem_or_mem hP with hP | hP
        · exact mem _ (D.ntw.placesOver_subset_exceptional i 0) hP
        · exact mem _ (D.ntw.placesOver_subset_exceptional i 1) hP
      · exact mem _ (by rw [h.ringSpec_excludedPlaces_eq i]; exact fun Q hQ => Or.inl (Or.inl (Or.inr hQ))) hP
    · exact mem _ (by rw [h.ringSpec_excludedPlaces_eq i]; exact fun Q hQ => Or.inl (Or.inr hQ)) hP

theorem conj_of_lev {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.IndefR.Lev.IsConjPl P P') : Formalism.BasicNotions.IsConjPl D.host P P' := by
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  let φ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hφ : ∀ x : 𝓞 D.host.E, ((φ x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := fun _ => rfl
  have le : P.asIdeal ≤ P'.asIdeal.comap φ := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have : φ c = c' := RingOfIntegers.ext (by rw [hφ, h2, hs])
    exact Ideal.mem_comap.2 (this ▸ h1)
  have e := P.isMaximal.eq_of_le (Ideal.comap_ne_top φ P'.isPrime.ne_top) le
  intro x y hxy
  have : y = φ x := RingOfIntegers.ext (by rw [hφ, hxy])
  rw [this, e]
  rfl

theorem baseTup_of {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw)
    (t : X.T) (ht : X.R.xiH t = X.R.C.delAt (D.ntw.l i)) : BaseTup Y i := fun j b => by
  have hL := X.char.lev
  refine ⟨t, (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 _ _ _ (ht ▸ hL.xi t) (Y.Z.pin.delta i j b), ?_⟩
  have hd : IsDelta (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) (X.R.xiH t) := by
    rw [ht, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have ram : ∀ P, ¬ (X.R.xiH t).UnrAt P ↔ P ∈ D.ntw.pD i := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
    refine ⟨fun h => by_contra fun h' => h (hd.unr P h'), fun h hu => ?_⟩
    have := (hd.ine P h 1).1 fun x hx => by rw [pow_one]; exact hu x hx
    omega
  have fw : ∀ P ∈ X.R.Q t, P ∈ D.ntw.pD i ∧ P ∈ Y.Z.ρ.ch i := fun P hP =>
    have h1 := (ram P).1 ((hL.Q_ram t P).2 (Or.inl hP))
    ⟨h1, Y.Z.pin.deltaPl i t P hP h1⟩
  rw [Y.Z.good.delta i j b]
  ext P
  change _ ↔ P ∈ half _ _
  refine Iff.trans ?_ (by classical simp only [half, Finset.mem_filter] : P ∈ D.ntw.pD i ∧ P ∈ Y.Z.ρ.ch i ↔ P ∈ half (Y.Z.ρ.ch i) (D.ntw.pD i))
  refine ⟨fw P, fun ⟨h1, h2⟩ => ?_⟩
  rcases (hL.Q_ram t P).1 ((ram P).2 h1) with h | ⟨P', h, hc⟩
  · exact h
  · by_cases e : P' = P
    · exact e ▸ h
    · exact absurd h2 (((Y.Z.good.ch i).pair P' P (conj_of_lev hc) e).1 (fw P' h).2)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

end General

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

def realOf (t : RowsT K w Z Wt p0) (hH : HostHyp (w.st Z).toD7) (hV : ∀ j, FWT.VStd (w.st Z).toD7 j)
    (hs : 8 * B.R.f * B.R.r + 4 ≤ B.R.nV) : RealSide (w.st Z).toD7 where
  Γ := _
  Pl0 := _
  I0 := _
  T := _
  A3 := _
  core := t.r.z.core
  R := t.r.z.R
  F := t.r.z.F
  cG := t.r.z.cG
  geo := t.r.z.geo
  char := RealDat3.characterisation_of_weak t.r.z.pins.char t.exAt
  phs := t.r.z.pins.phs
  guard := t.r.z.pins.keep.guard
  valKs := t.r.z.pins.keep.valKs
  idem := t.r.z.good.2
  unif := t.r.intersectionNumber_baseChange.prim.unif
  integral := t.r.intersectionNumber_baseChange.aux.integral
  inGeo := t.inGeo
  finT := Finite.of_injective _ (R3.ixOf_injective w.I _)
  host := hH
  std := hV
  size := hs

variable {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} {xd : ThData (w.D Z)} {c : NCore hL t n}

def twOf {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd))
    (hS : Y.S = ratDatR t.r.z.R t.r.z.cG c.row.kKs c.row.hk) (hY : HEq Y.YS c.row.nexp) (g : GalSide (w.st Z).toD7)
    (h1 : g.cf = TC.cf w.I w.l Z) (h2 : g.lam.C = TC.cf w.I w.l Z) (hF : FieldOk (realOf t hH hV hs))
    (cg : CGTrue hL (w.st Z).toD7 g.wd)
    (hb : T = TwDat.untw B T.pl → ∀ v, (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 → BaseTup Y (nch.twI v)) :
    TwOf hL K B f T w Z Wt p0 t nch n xd c :=
  ⟨realOf t hH hV hs, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, Y, hS, hY, g,
    h1, h2, t.r.z.lev.C, hF, cg, hb⟩

def serOf {hH hV hs} (e : NE hL K B f T w Z Wt p0 t nch n xd c)
    (H : NExpRealH t.r.z.R t.r.z.cG _ c.row.nexp) (hr : GlobalTheory.ExportPin.Reads t.r.z.R t.r.z.cG _ c.row.nexp H.hL)
    (hd : ∀ i b P, P ∉ (w.D Z).ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G (w.D Z).host.E (w.D Z).nd.Om,
      Formalism.ConjugateSelfDual.IsFrob (F := (w.D Z).host.E) ((w.D Z).nd.plOm.1 P) (Formalism.ConjugateSelfDual.normV P) σ →
      H.cHk i b 1 P = algebraMap ((w.D Z).ntw.O i) (FractionRing ((w.D Z).ntw.O i)) (algebraMap ((w.D Z).ntw.O0 i) ((w.D Z).ntw.O i)
        ((if b then (w.D Z).ntw.delta i σ else ((w.D Z).ntw.delta i σ)⁻¹ : ((w.D Z).ntw.O0 i)ˣ) : (w.D Z).ntw.O0 i)))
    (hk_emb : ∀ i j b k P (x : (w.D Z).ntw.B i j b), 1 ≤ j → j ≤ B.R.m → IntegralHeckeForms.HkIdx i k P →
      (w.D Z).nexp.embB i j b ((w.D Z).ntw.hk i j b k P x) = (w.D Z).nexp.hkF i j b k P ((w.D Z).nexp.embB i j b x))
    (hz : ∀ i (s : (w.D Z).ntw.Sig i) P, (w.D Z).ntw.hEig i s 0 P = 1) : SerSide (realOf t hH hV hs) (twEOf xd) where
  S := _
  YS := c.row.nexp
  sup := e.ser.sup
  H := H
  reads := hr
  del := hd
  Z := e.ser.ex
  U_eq g := (c.row.grp.lvl0 g).symm
  psi_eq := psi_of_grp c.row.grp e.ser.ex
  low := low_of_tied c.a.all.tw (q_dvd_discr _)
  Sb i P hP := by
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.D Z).ntw.placesOver_subset_exceptional i k hk
  B_range i _ j _ b := c.a.all.tw.B_range i j b
  hk_emb := hk_emb
  hk_split i _ j _ b k P h := by
    obtain ⟨s, hs⟩ := c.a.all.tw.hk_split i j b k P h.2.2.2
    exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
      exact Polynomial.Splits.X_sub_C a
  off i _ := ⟨fun j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), hz i⟩
  all i j hj b a := by
    have := e.xd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    change a ∈ xd.xd0 i j b
    rw [this]; trivial

theorem base_of_untw {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd)) (hT : T = TwDat.untw B T.pl) (v : B.places.Pl)
    (hv : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0) : BaseTup Y (nch.twI v) := by
  refine baseTup_of Y _ (t.r.z.R.mu ((w.D Z).plEq v)) ?_
  have hW : v ∈ Wt := by_contra fun h => hv (t.mu.off v h)
  have h1 := (t.r.z.mu v).2
  rw [if_pos hW] at h1
  have hp : T.psi v = 1 := by rw [hT]; rfl
  refine ((t.r.z.lev.xiH _).trans h1).trans ?_
  refine Eq.trans ?_ (congrArg₂ CharFrame.delAt t.r.z.lev.C (nch.twI_l v)).symm
  unfold TwDat.xiTw
  rw [hp, mul_one]
  rfl

theorem wd_of_built {D : D7} (b : NBuilt hL D) :
    ∃ wd : GlobalTheory.RowTie.WDTie D.nd D.naut, Nonempty (CGTrue hL D wd) ∧ LabTrue D wd := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨{ A.wdT with }, ⟨{ cg with }⟩, A.lab⟩

theorem gal_of (e : NE hL K B f T w Z Wt p0 t nch n xd c) (h3 : GlobalTheory.Triple.IsTriple (w.D Z)) (hr : 100 ≤ B.R.r)
    (hg : ∀ k, 2 * B.R.r ≤ B.host.g k) : ∃ g : GalSide (w.st Z).toD7, g.cf = TC.cf w.I w.l Z ∧ g.lam.C = TC.cf w.I w.l Z ∧
      Nonempty (CGTrue hL (w.st Z).toD7 g.wd) := by
  obtain ⟨wd, cg, lab⟩ := wd_of_built c.a.nt.toNBuilt
  exact ⟨⟨wd, lab, TC.cf w.I w.l Z, { c.a.chrN with }, h3, e.ser.lam, e.ser.lam_ok, fun i hi => (e.ser.lam_tie i hi).imp id (Exists.imp fun _ h => ⟨h.1, h.2.1⟩), hr, hg⟩, rfl, e.ser.lam_C, cg⟩

theorem hk_of_built {D : D7} (b : NBuilt hL D) :
    (∀ i j s k P (x : D.ntw.B i j s), 1 ≤ j → j ≤ D.R.m → IntegralHeckeForms.HkIdx i k P →
      D.nexp.embB i j s (D.ntw.hk i j s k P x) = D.nexp.hkF i j s k P (D.nexp.embB i j s x)) ∧
    ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1 := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨fun i j s k P x h1 h2 h => Bs.hk_emb i j s k P x h1 h2 h.2.2.2 h.2.2.1 h.2.1, Bs.hEig_zero⟩

theorem nonempty_of_more {hH hV hs} (e : NE hL K B f T w Z Wt p0 t nch n xd c) (hF : FieldOk (realOf t hH hV hs))
    (h3 : GlobalTheory.Triple.IsTriple (w.D Z)) (hr : 100 ≤ B.R.r) (hg : ∀ k, 2 * B.R.r ≤ B.host.g k)
    (H : NExpRealH t.r.z.R t.r.z.cG _ c.row.nexp) (hR : GlobalTheory.ExportPin.Reads t.r.z.R t.r.z.cG _ c.row.nexp H.hL)
    (hd : ∀ i b P, P ∉ (w.D Z).ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G (w.D Z).host.E (w.D Z).nd.Om,
      Formalism.ConjugateSelfDual.IsFrob (F := (w.D Z).host.E) ((w.D Z).nd.plOm.1 P) (Formalism.ConjugateSelfDual.normV P) σ →
      H.cHk i b 1 P = algebraMap ((w.D Z).ntw.O i) (FractionRing ((w.D Z).ntw.O i)) (algebraMap ((w.D Z).ntw.O0 i) ((w.D Z).ntw.O i)
        ((if b then (w.D Z).ntw.delta i σ else ((w.D Z).ntw.delta i σ)⁻¹ : ((w.D Z).ntw.O0 i)ˣ) : (w.D Z).ntw.O0 i))) :
    Nonempty (TwOf hL K B f T w Z Wt p0 t nch n xd c) := by
  obtain ⟨g, h1, h2, ⟨cg⟩⟩ := gal_of e h3 hr hg
  obtain ⟨k1, k2⟩ := hk_of_built c.a.nt.toNBuilt
  exact ⟨twOf (serOf e H hR hd k1 k2) rfl HEq.rfl g h1 h2 hF cg fun hT v hv => base_of_untw _ hT v hv⟩

def ofExt (a : TwExt hL K B f T w Z Wt p0 t nch n xd c) : TwOf hL K B f T w Z Wt p0 t nch n xd c := ofAt a

theorem twOf_xdAll (a : TwOf hL K B f T w Z Wt p0 t nch n xd c) : XdAll xd := (elim a).2.2.2.2.1

end Rows

end GlobalTheory.TwInputs.JoinModel

end
