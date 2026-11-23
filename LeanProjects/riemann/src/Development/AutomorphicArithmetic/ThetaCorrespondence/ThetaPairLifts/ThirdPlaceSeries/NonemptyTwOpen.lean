import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitTw
variable {D : D7}
set_option maxHeartbeats 4000000 in
def chrL_alt {L : LocAll (lay0 D)} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tp : TupTied D cf C} {iq : ∀ i : L.X.nd.Loc, FractionRing (L.X.nd.O i) →+* Qbar (L.X.nd.l i)}
    (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup iq L.Y L.C) : NCharTied (withLoc L) (cfL L cf) (chL L C) (tpL L tp) :=
  { A.chr with muC := Au.muC }
set_option maxHeartbeats 8000000 in
theorem nonempty_twOpen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), Nonempty (TwOpen (withLoc L) (chL L C) (cfL L cf) (tpL L tp) (mtL L M) low) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp ch _ _ _ _ _ big L Sp Au
  have ch' := chSideL Sp ch
  let K := chiDL L Bs.chiD (fun a => toHC ((tpL L tp).psi ((withLoc L).nd.w a)))
  have h0 : ∀ x, K.etaT.χ x = (cfL L cf).eta.1 x := Bs.eta_eq
  have h1 : ∀ (j : Fin (withLoc L).R.m) x, (K.mu0 (j.1 + 1)).χ x = ((cfL L cf).mu0 j).1 x := Bs.ringSpec_normalisedCharacter_eq
  have h2 : ∀ s x, (K.del s).χ x = ((cfL L cf).delAt ((withLoc L).ntw.l s)).1 x := Bs.del_eq
  have h3 : ∀ a x, (K.psi a).χ x = ((tpL L tp).psi ((withLoc L).nd.w a)).1 x := fun _ _ => rfl
  have hg := psiL_gal' (_root_.GlobalTheory.HeightCounting.FitTw.chrL_alt Au) ch'.nct ch'.psi K h0 h1 h2 Bs.chi.chi1
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
    etaT_link := etaT_link (_root_.GlobalTheory.HeightCounting.FitTw.chrL_alt Au) _ h0
    muC_link := fun i => Filter.Eventually.of_forall fun w => muC_link (_root_.GlobalTheory.HeightCounting.FitTw.chrL_alt Au) K h1 h2 h3 i w
    iCq_embO := Bs.iCq_embO
    embO_star := Bs.embO_star
    chrN := _root_.GlobalTheory.HeightCounting.FitTw.chrL_alt Au
    chrGal := ⟨hp, hg, deltaReadL L Bs.deltaRead⟩ }⟩
end GlobalTheory.HeightCounting.FitTw
end
end
