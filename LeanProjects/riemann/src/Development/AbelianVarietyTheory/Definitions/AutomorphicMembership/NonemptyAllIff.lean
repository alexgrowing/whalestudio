import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EMtLevel
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

noncomputable section

namespace GlobalTheory.HeightCounting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.L2 Formalism.L2.NT

set_option synthInstance.maxHeartbeats 400000 in

structure NAllC (D : D7) (C : NChoice D) where
  gal : NGalTied D
  n : NormalizedHeckeDataPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

def GoodCl (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w →
    (Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →
    ExpGood D I (avD D (avDesign D) (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D}

def NAllC.toAll (A : NAllC D C) (h : GoodCl D C I) : NormalizedTwistCompatibility D C I :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, h, A.choice.conj⟩ }

def NAllC.ofAll (A : NormalizedTwistCompatibility D C I) : NAllC D C :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, A.choice.conj⟩ }

theorem goodCl_of_all (A : NormalizedTwistCompatibility D C I) : GoodCl D C I := A.choice.good

theorem nonempty_all_iff : Nonempty (NormalizedTwistCompatibility D C I) ↔ Nonempty (NAllC D C) ∧ GoodCl D C I :=
  ⟨fun ⟨A⟩ => ⟨⟨NAllC.ofAll A⟩, goodCl_of_all A⟩, fun ⟨⟨A⟩, h⟩ => ⟨A.toAll h⟩⟩

example (A : NAllC D C) (h : GoodCl D C I) : NAllC.ofAll (A.toAll h) = A := rfl

example (A : NormalizedTwistCompatibility D C I) : (NAllC.ofAll A).toAll (goodCl_of_all A) = A := rfl

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

structure PhtOn {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (Wd : WDSide D T) (fr : OmFrame D)
    (p : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ), (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → Prop) : Prop where
  card : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (τ : D.host.E →+* Qbar l) (w : PlE D.host), p l a r →
    (∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) → Wd.IsdRW l ι r w → Multiset.card (Wd.jumpsW l ι r τ) = a

def PhtCmp : Prop :=
  ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T), PhtOn Wd fr fun l _ a r =>
    Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))

def LpCmp (_hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  ∀ (D : D7) (_T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (LPTiedPlaceholder D)

def CgCmp (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → Nonempty (NormalizedHeckeDataPlaceholder D)

structure ArchCmp (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop where
  pht : PhtCmp
  lp : LpCmp hL
  cg : CgCmp hL

end GlobalTheory.HeightCounting

end
