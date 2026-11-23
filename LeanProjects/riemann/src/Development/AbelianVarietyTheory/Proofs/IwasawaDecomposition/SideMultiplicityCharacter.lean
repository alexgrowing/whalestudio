import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}

set_option maxHeartbeats 2000000 in

def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }

set_option maxHeartbeats 4000000 in
theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }

set_option maxHeartbeats 4000000 in
theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }

set_option maxHeartbeats 20000000 in

def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real

set_option maxHeartbeats 4000000 in

def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }

set_option maxHeartbeats 4000000 in
theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) where
  twOf_eq := Sp.twOf_eq
  twSide_eq := Sp.twSide_eq
  Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  psi_eq := by
    obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
    exact ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
  embedding_baseField_condition := h.embedding_baseField_condition

set_option maxHeartbeats 4000000 in
theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) where
  nct := nctL Sp h.nct
  choice := choiceL L h.choice
  off := h.off
  adm := h.adm
  psi := h.psi
  eMt_level := h.eMt_level

set_option maxHeartbeats 4000000 in

def chrL {L : LocAll (lay0 D)} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tp : TupTied D cf C} {iq : ∀ i : L.X.nd.Loc, FractionRing (L.X.nd.O i) →+* Qbar (L.X.nd.l i)}
    (Au : AutSpec A M tp.tup iq L.Y L.C) : NCharTied (withLoc L) (cfL L cf) (chL L C) (tpL L tp) :=
  { A.chr with muC := Au.muC }

set_option maxHeartbeats 4000000 in

def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }

set_option maxHeartbeats 4000000 in
theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }

set_option maxHeartbeats 4000000 in
theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h

set_option maxHeartbeats 8000000 in

theorem nonempty_twOpen : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : AutSpec A M tp.tup Sp.iq L.Y L.C), Nonempty (TwOpen (withLoc L) (chL L C) (cfL L cf) (tpL L tp) (mtL L M) low) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp ch _ _ _ _ _ big L Sp Au
  have ch' := chSideL Sp ch
  let K := chiDL L Bs.chiD (fun a => toHC ((tpL L tp).psi ((withLoc L).nd.w a)))
  have h0 : ∀ x, K.etaT.χ x = (cfL L cf).eta.1 x := Bs.eta_eq
  have h1 : ∀ (j : Fin (withLoc L).R.m) x, (K.mu0 (j.1 + 1)).χ x = ((cfL L cf).mu0 j).1 x := Bs.ringSpec_normalisedCharacter_eq
  have h2 : ∀ s x, (K.del s).χ x = ((cfL L cf).delAt ((withLoc L).ntw.l s)).1 x := Bs.del_eq
  have h3 : ∀ a x, (K.psi a).χ x = ((tpL L tp).psi ((withLoc L).nd.w a)).1 x := fun _ _ => rfl
  have hg := psiL_gal' (chrL Au) ch'.nct ch'.psi K h0 h1 h2 Bs.chi.chi1
  have hp := psi_is (tpL L tp) ch'.nct
  exact ⟨{
    chiD := K
    chi := chiL L Bs.chi _ fun a => psiL_read a _ (fun v hv => ((hp a).ram v).2 hv) (hg a)
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    exp := expL L Bs.exp
    ch := ch'
    eta_eq := h0
    ringSpec_normalisedCharacter_eq := h1
    del_eq := h2
    psi_eq := h3
    etaT_link := etaT_link (chrL Au) _ h0
    muC_link := fun i => Filter.Eventually.of_forall fun w => muC_link (chrL Au) K h1 h2 h3 i w
    iCq_embO := Bs.iCq_embO
    embO_star := Bs.embO_star
    chrN := chrL Au
    chrGal := ⟨hp, hg, deltaReadL L Bs.deltaRead⟩ }⟩

end GlobalTheory.HeightCounting.FitTw

end
