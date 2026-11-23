import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]

set_option synthInstance.maxHeartbeats 400000 in

structure TwR (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) where
  cc : N.Om ≃+* N.Om
  cc_cm : IsCMConjOm H.E N.Om cc
  Tw : Type
  l : Tw → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]
  O0 : Tw → Type
  [crO0 : ∀ i, CommRing (O0 i)]
  [twistBaseCoefficientRing_isDomain : ∀ i, IsDomain (O0 i)]
  [twistBaseCoefficientRing_isDVR : ∀ i, IsDiscreteValuationRing (O0 i)]
  [algO0 : ∀ i, Algebra ℤ_[l i] (O0 i)]
  [twistBaseCoefficientRing_finite_padic : ∀ i, Module.Finite ℤ_[l i] (O0 i)]
  twistBaseCoefficientRing_residueField_finite : ∀ i, Finite (IsLocalRing.ResidueField (O0 i))
  [topO0 : ∀ i, TopologicalSpace (O0 i)]
  [twistBaseCoefficientRing_topologicalRing : ∀ i, IsTopologicalRing (O0 i)]
  twistBaseCoefficientRing_isAdic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O0 i))
  emb0 : ∀ i, LL0 →+* FractionRing (O0 i)
  emb0b : ∀ i, LL0 →+* FractionRing (O0 i)
  restX_coefficientEmbedding_conj : ∀ i (x y : LL0), (y : what₂.LL) = star (x : what₂.LL) → emb0b i x = emb0 i y
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra (O0 i) (O i)]
  O_inj : ∀ i, Function.Injective (algebraMap (O0 i) (O i))
  O_l : ∀ i, ((l i : ℕ) : O i) ∈ IsLocalRing.maximalIdeal (O i)
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  resO_ac : ∀ i, IsAlgClosed (IsLocalRing.ResidueField (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)
  Ok : Tw → ℕ → Type
  [crOk : ∀ i k, CommRing (Ok i k)]
  [domOk : ∀ i k, IsDomain (Ok i k)]
  [dvrOk : ∀ i k, IsDiscreteValuationRing (Ok i k)]
  [algOk : ∀ i k, Algebra (O i) (Ok i k)]
  Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k))
  Ok_fin : ∀ i k, Module.Finite (O i) (Ok i k)
  zk : ∀ i k, (Ok i k)ˣ
  zk_prim : ∀ i k, IsPrimitiveRoot ((zk i k : Ok i k)) (l i ^ k)
  Ok_gen : ∀ i k (x : FractionRing (Ok i k)), ∃ p : Polynomial (O i), ∃ d : O i, d ≠ 0 ∧
    x * algebraMap (Ok i k) (FractionRing (Ok i k)) (algebraMap (O i) (Ok i k) d) =
      algebraMap (Ok i k) (FractionRing (Ok i k)) (Polynomial.aeval (zk i k : Ok i k) p)
  pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  pD_eq : ∀ i, (pD i : Set (HeightOneSpectrum (𝓞 H.E))) =
    placesOver H.E (if l i = H.pde then H.pde' else H.pde)
  delta : ∀ i, G H.E N.Om →* (O0 i)ˣ
  delta_open : ∀ i, IsOpen ((delta i).ker : Set (G H.E N.Om))
  delta_anti : ∀ i, AntiHom cc (delta i)
  delta_ram : ∀ i, RamExactly (delta i) ↑(pD i)
  delta_15 : ∀ i, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := H.E) A).map (delta i)) = 15
  delta_tame : ∀ i, ∀ v ∈ pD i, Ideal.absNorm v.asIdeal % 15 = 1
  chi1 : ∀ i, ℕ → Bool → (G H.E N.Om →* (O0 i)ˣ)
  twistCharacterFamily_continuous : ∀ i j b, Continuous (fun g => ((chi1 i j b g : (O0 i)ˣ) : O0 i))
  twistCharacterFamily_unramified : ∀ i j b v, v ∉ placesOver H.E (l i) → (∀ k, v ∉ placesOver H.E (H.g k)) → v ∉ pD i →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, chi1 i j b σ = 1
  twistCharacterFamily_at_auxiliaryPlaces : ∀ i j b, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, chi1 i j b σ = if b then delta i σ else (delta i σ)⁻¹
  twistCharacterFamily_tame : ∀ i j b k v, v ∈ placesOver H.E (H.g k) → v ∉ placesOver H.E (l i) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      chi1 i j b σ ^ (H.g k - 1) = 1
  S0 : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  twistExcludedPlaces_contains_residueChar : ∀ i, placesOver H.E (l i) ⊆ ↑(S0 i)
  placesOver_subset_exceptional : ∀ i k, placesOver H.E (H.g k) ⊆ ↑(S0 i)
  primes_subset_exceptional : ∀ i, pD i ⊆ S0 i
  RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ i Q, CommGroup (RCG i Q)]
  [finRCG : ∀ i Q, Fintype (RCG i Q)]
  RCG_l : ∀ i Q (x : RCG i Q), ∃ n : ℕ, x ^ (l i ^ n) = 1
  art : ∀ i Q, G H.E N.Om →* RCG i Q
  art_surj : ∀ i Q, Function.Surjective (art i Q)
  art_cont : ∀ i Q, IsOpen ((art i Q).ker : Set (G H.E N.Om))
  art_anti : ∀ i Q, AntiHom cc (art i Q)
  art_unr : ∀ i Q v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art i Q σ = 1
  art_univ : ∀ i Q, (∀ v ∈ Q, v ∉ placesOver H.E (l i)) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l i ^ n) = 1) → ∀ φ : G H.E N.Om →* A',
    IsOpen (φ.ker : Set (G H.E N.Om)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG i Q →* A', f.comp (art i Q) = φ
  res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG i Q →* RCG i Q')
  res_art : ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (art i Q) = art i Q'

attribute [instance] TwR.lPrime TwR.crO0 TwR.twistBaseCoefficientRing_isDomain TwR.twistBaseCoefficientRing_isDVR TwR.algO0 TwR.twistBaseCoefficientRing_finite_padic TwR.topO0 TwR.twistBaseCoefficientRing_topologicalRing TwR.crO TwR.domO TwR.dvrO TwR.algO TwR.topO TwR.trO TwR.crOk TwR.domOk TwR.dvrOk TwR.algOk TwR.grpRCG TwR.finRCG

variable {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure TwF (T : TwR LL0 N) where
  Sig : T.Tw → Type
  [finSig : ∀ i, Fintype (Sig i)]
  jS : ∀ i, Sig i → ℕ
  jS_range : ∀ i s, 1 ≤ jS i s ∧ jS i s ≤ R.m
  side : ∀ i, Sig i → Bool
  rhoS : ∀ i, Sig i → (G H.E N.Om →* GL (Fin R.r) (T.O0 i))
  rhoS_cont : ∀ i s, Continuous (fun g => ((rhoS i s g : GL (Fin R.r) (T.O0 i)) :
    Matrix (Fin R.r) (Fin R.r) (T.O0 i)))
  B : T.Tw → ℕ → Bool → Type
  [acgB : ∀ i j b, AddCommGroup (B i j b)]
  [modB : ∀ i j b, Module (T.O i) (B i j b)]
  [freeB : ∀ i j b, Module.Free (T.O i) (B i j b)]
  [finB : ∀ i j b, Module.Finite (T.O i) (B i j b)]
  Theta : ∀ i j b, Submodule (T.O i) (B i j b)
  ThetaPsi : ∀ i j b k, Finset (HeightOneSpectrum (𝓞 H.E)) → (G H.E N.Om →* (T.Ok i k)ˣ) →
    Submodule (T.Ok i k) (TensorProduct (T.O i) (T.Ok i k) (B i j b))
  ThetaPsi_one : ∀ i j b k, ThetaPsi i j b k ∅ 1 = (Theta i j b).baseChange (T.Ok i k)
  hk : ∀ i j b, ℕ → HeightOneSpectrum (𝓞 H.E) → Module.End (T.O i) (B i j b)
  hk_zero : ∀ i j b P, hk i j b 0 P = 1
  hEig : ∀ i, Sig i → ℕ → HeightOneSpectrum (𝓞 H.E) → T.O i

set_option synthInstance.maxHeartbeats 400000 in

structure TwL (T : TwR LL0 N) where
  abelian₂ : T.Tw → Type
  [finLam : ∀ i, Fintype (abelian₂ i)]
  jL : ∀ i, abelian₂ i → ℕ
  sideL : ∀ i, abelian₂ i → Bool
  s2 : ∀ i, abelian₂ i → ℤ
  jL_range : ∀ i lam, 1 ≤ jL i lam ∧ jL i lam ≤ R.m
  lamG : ∀ i, abelian₂ i → (G H.E N.Om →* (T.O i)ˣ)
  lamG_cont : ∀ i lam, Continuous (fun g => ((lamG i lam g : (T.O i)ˣ) : T.O i))
  lamG_unr : ∀ i lam v, v ∉ T.S0 i → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, lamG i lam σ = 1
  lamG_pD : ∀ i lam, ∀ v ∈ T.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, ∃ n : ℕ,
      (lamG i lam σ * (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
        (if sideL i lam then T.delta i σ else (T.delta i σ)⁻¹))⁻¹) ^ (Ideal.absNorm v.asIdeal ^ n) = 1
  lamG_anti : ∀ i lam, AntiHom T.cc (lamG i lam)
  Xv : ∀ i, abelian₂ i → HeightOneSpectrum (𝓞 H.E) → T.O i
  Xv_def : ∀ i lam P, P ∉ T.S0 i → ∀ σ : G H.E N.Om, IsFrob (F := H.E) (N.plOm.1 P) (normV P) σ →
    Xv i lam P = ((lamG i lam σ : (T.O i)ˣ) : T.O i)
  qs : ∀ i, abelian₂ i → HeightOneSpectrum (𝓞 H.E) → FractionRing (T.O i)
  qs_sq : ∀ i lam P, P ∉ T.S0 i → qs i lam P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(s2 i lam))
  qs_conj : ∀ i lam P P', IsConjPl H P P' → qs i lam P = qs i lam P'
  th : ∀ i Q, abelian₂ i → T.RCG i Q → FractionRing (T.O i)

def TwR.ntw (hE : IsEmpty N.Loc) (T : TwR LL0 N) (F : TwF T) (Λ : TwL T) : NTw R H what₂ LL0 N where
    cc := T.cc
    cc_cm := T.cc_cm
    Tw := T.Tw
    l := T.l
    lPrime := T.lPrime
    O0 := T.O0
    crO0 := T.crO0
    twistBaseCoefficientRing_isDomain := T.twistBaseCoefficientRing_isDomain
    twistBaseCoefficientRing_isDVR := T.twistBaseCoefficientRing_isDVR
    algO0 := T.algO0
    twistBaseCoefficientRing_finite_padic := T.twistBaseCoefficientRing_finite_padic
    twistBaseCoefficientRing_residueField_finite := T.twistBaseCoefficientRing_residueField_finite
    topO0 := T.topO0
    twistBaseCoefficientRing_topologicalRing := T.twistBaseCoefficientRing_topologicalRing
    twistBaseCoefficientRing_isAdic := T.twistBaseCoefficientRing_isAdic
    emb0 := T.emb0
    emb0b := T.emb0b
    restX_coefficientEmbedding_conj := T.restX_coefficientEmbedding_conj
    O := T.O
    crO := T.crO
    domO := T.domO
    dvrO := T.dvrO
    algO := T.algO
    O_inj := T.O_inj
    O_l := T.O_l
    topO := T.topO
    trO := T.trO
    O_adic := T.O_adic
    resO_ac := T.resO_ac
    O_complete := T.O_complete
    Ok := T.Ok
    crOk := T.crOk
    domOk := T.domOk
    dvrOk := T.dvrOk
    algOk := T.algOk
    Ok_inj := T.Ok_inj
    Ok_fin := T.Ok_fin
    zk := T.zk
    zk_prim := T.zk_prim
    Ok_gen := T.Ok_gen
    pD := T.pD
    pD_eq := T.pD_eq
    delta := T.delta
    delta_open := T.delta_open
    delta_anti := T.delta_anti
    delta_ram := T.delta_ram
    delta_15 := T.delta_15
    delta_tame := T.delta_tame
    chi1 := T.chi1
    twistCharacterFamily_continuous := T.twistCharacterFamily_continuous
    twistCharacterFamily_unramified := T.twistCharacterFamily_unramified
    twistCharacterFamily_at_auxiliaryPlaces := T.twistCharacterFamily_at_auxiliaryPlaces
    twistCharacterFamily_tame := T.twistCharacterFamily_tame
    S0 := T.S0
    twistExcludedPlaces_contains_residueChar := T.twistExcludedPlaces_contains_residueChar
    placesOver_subset_exceptional := T.placesOver_subset_exceptional
    primes_subset_exceptional := T.primes_subset_exceptional
    RCG := T.RCG
    grpRCG := T.grpRCG
    finRCG := T.finRCG
    RCG_l := T.RCG_l
    art := T.art
    art_surj := T.art_surj
    art_cont := T.art_cont
    art_anti := T.art_anti
    art_unr := T.art_unr
    art_univ := T.art_univ
    res := T.res
    res_art := T.res_art
    Sig := F.Sig
    finSig := F.finSig
    jS := F.jS
    jS_range := F.jS_range
    side := F.side
    rhoS := F.rhoS
    rhoS_cont := F.rhoS_cont
    B := F.B
    acgB := F.acgB
    modB := F.modB
    freeB := F.freeB
    finB := F.finB
    Theta := F.Theta
    ThetaPsi := F.ThetaPsi
    ThetaPsi_one := F.ThetaPsi_one
    hk := F.hk
    hk_zero := F.hk_zero
    hEig := F.hEig
    abelian₂ := Λ.abelian₂
    finLam := Λ.finLam
    jL := Λ.jL
    sideL := Λ.sideL
    s2 := Λ.s2
    jL_range := Λ.jL_range
    lamG := Λ.lamG
    lamG_cont := Λ.lamG_cont
    lamG_unr := Λ.lamG_unr
    lamG_pD := Λ.lamG_pD
    lamG_anti := Λ.lamG_anti
    Xv := Λ.Xv
    Xv_def := Λ.Xv_def
    qs := Λ.qs
    qs_sq := Λ.qs_sq
    qs_conj := Λ.qs_conj
    th := Λ.th
    twOf := fun a => hE.elim a
    twSide := fun a => hE.elim a
    twOf_l := fun a => hE.elim a
    twist₂ := fun a => hE.elim a
    twO_emb := fun a => hE.elim a
    psiL := fun a => hE.elim a
    psiL_ord := fun a => hE.elim a
    psiL_open := fun a => hE.elim a
    psiL_anti := fun a => hE.elim a
    psiL_ram := fun a => hE.elim a
    psiL_l := fun a => hE.elim a
    chi_tw := fun a => hE.elim a

def TwL.empty (T : TwR LL0 N) : TwL T where
  abelian₂ := fun _ => PEmpty
  jL := fun _ a => a.elim
  sideL := fun _ a => a.elim
  s2 := fun _ a => a.elim
  jL_range := fun _ a => a.elim
  lamG := fun _ a => a.elim
  lamG_cont := fun _ a => a.elim
  lamG_unr := fun _ a => a.elim
  lamG_pD := fun _ a => a.elim
  lamG_anti := fun _ a => a.elim
  Xv := fun _ a => a.elim
  Xv_def := fun _ a => a.elim
  qs := fun _ a => a.elim
  qs_sq := fun _ a => a.elim
  qs_conj := fun _ a => a.elim
  th := fun _ _ a => a.elim

def NLay0.setTw (L : NLay0 R H what₂ LL0) (tw : NTw R H what₂ LL0 L.nd) (ex : NExp R H what₂ LL0 L.nd tw)
    (h0 : ∀ g : G0g L.nd, what₂.embLL ((ex.eLL0 g : ↥LL0) : what₂.LL) = L.ntypes.e0.coeff g)
    (th : NTh R H what₂ LL0 L.nd tw ex)
    (br : ∀ (i : tw.Tw) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (tw.l i) →
      Formalism.BasicNotions.LocBridge (tw.l i) H.E L.nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (L.nd.plOm.1 w)) (tw.O0 i))
    (hbr : ∀ (i : tw.Tw) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (tw.l i))
      (x : L.nd.Om), x ∈ L.nd.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1) : NLay0 R H what₂ LL0 :=
  { L with ntw := tw, nexp := ex, nStage_trivialCharacter_coeff_eq := h0, nth := th, ntwbr := br, ntwbr_ind := hbr }

def setTw (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw)
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd tw ex)
    (br : ∀ (i : tw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Formalism.BasicNotions.placesOver D.host.E (tw.l i) →
      Formalism.BasicNotions.LocBridge (tw.l i) D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (tw.O0 i))
    (hbr : ∀ (i : tw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (tw.l i))
      (x : D.nd.Om), x ∈ D.nd.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1) : D7 :=
  { D with ntw := tw, nexp := ex, nStage_trivialCharacter_coeff_eq := h0, nth := th, ntwbr := br, ntwbr_ind := hbr }

end GlobalTheory.HeightCounting

end
