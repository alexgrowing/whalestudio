import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdTie
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdStd
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdProj
import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeLift0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

def mt0 (M : MtFam D) : MtFam0 D.host D.what₂ := fun μ j h1 h2 =>
  { wt := (M μ j h1 h2).wt, J := (M μ j h1 h2).J, χ := (M μ j h1 h2).χ, J_open := (M μ j h1 h2).J_open,
    real := (M μ j h1 h2).real, real_inj := (M μ j h1 h2).real_inj, real_range := (M μ j h1 h2).real_range }

theorem genAt_iff (l : ℕ) (Q : Finset (PlE D.host)) (v : PlE D.host) (k : ℕ) :
    GenAt D l Q v k ↔ GenAt0 D.host l Q v k := Iff.rfl

def plEmb (pl : PlSide D) : PlEmb D.what₂ where
  emb w := (pl.ι w).symm.toRingHom.comp D.what₂.embLL
  emb_w w x := pl.ι_w w x

def coefIn (pl : PlSide D) (Kx : ∀ (_ : ℕ) (w : D.what₂.places.Pl), Loc.FinExt (D.what₂.places.resChar w))
    (hKx : ∀ j w (x : D.what₂.LL), (plEmb pl).emb w x ∈ (Kx j w).1) : CoefIn D.what₂ :=
  ⟨plEmb pl, Kx, hKx⟩

def QOver (C : NChoice D) : Prop := ∀ w (v v' : PlE D.host), v ∈ C.Q w →
  (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ C.Q w

def QConj (C : NChoice D) : Prop := ∀ w (v v' : PlE D.host), v' ∈ C.Q w → IsConjPl D.host v v' → v ∈ C.Q w

def nbase (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂)
    (hS : SplitK (mt0 M) C.Q hR X) (hO : QOver C) (hc : QConj C) : NLocBase D M where
  Oc := OcC X
  ec := ecC X
  ec_w := ecC_w X
  V := VC X
  iV := iVC X
  iV_basis := iVC_basis X
  Qc _ w := C.Q w
  hL := hLC (mt0 M) C.Q hR
  hL_def j w h1 h2 v k s ϖ hg hcj hu x := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x
  hK := hKC (mt0 M) C.Q hR X
  hK_def := hKC_def (mt0 M) C.Q hR X
  split j w v k hg := hS j w v k hg
  Qc_over _ w := hO w
  Qc_conj _ w := hc w

abbrev base (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂)
    (hS : SplitK (mt0 M) C.Q hR X) : LocBase0 D.host D.what₂ :=
  baseC (mt0 M) C.Q hR X hS

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def HeckeIntTw (B : LocBase0 H what₂) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ R.m → what₂.muAt w ≠ what₂.mu0 → ∀ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k →
    ∀ x ∈ {x : what₂.MtL (what₂.muTw w) j | what₂.jMt (what₂.muTw w) j x ∈ (what₂.MtLat (what₂.muTw w) j).gen}, ∃ (F : Finset (what₂.MtL (what₂.muTw w) j)) (c : what₂.MtL (what₂.muTw w) j → what₂.LL),
      (↑F ⊆ {x : what₂.MtL (what₂.muTw w) j | what₂.jMt (what₂.muTw w) j x ∈ (what₂.MtLat (what₂.muTw w) j).gen}) ∧ (∀ y ∈ F, 0 ≤ what₂.places.val w (c y)) ∧ B.hL j w v k x = ∑ y ∈ F, c y • y

def SemisimpleTw (B : LocBase0 H what₂) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ R.m → what₂.muAt w ≠ what₂.mu0 → ∀ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k →
    (B.hK j w v k).IsSemisimple

def ActHK (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd))
    (hAct : ActEx B (partCompl_of hs hd)) : Prop :=
  ∀ (i : LocT B) v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k → ∀ z,
    PsiC B (partCompl_of hs hd) hL i
      (((actC B (partCompl_of hs hd) hAct i) (hTOf B i v k)).baseChange (FractionRing (OOf B i)) z) =
    B.hK (jOf B i) (wOf B i) v k (PsiC B (partCompl_of hs hd) hL i z)

end Gen

section Loc

variable (B0 : LocBase0 D.host D.what₂)

def chi1N (C : NChoice D) (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
    (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ) (i : LocT B0) : G D.host.E D.nd.Om →* (OOf B0 i)ˣ :=
  (Units.map (tw i).toMonoidHom).comp (D.ntw.chi1 (C.twI (wOf B0 i)) (jOf B0 i) (C.sd (wOf B0 i))) * ps i

def chiN (C : NChoice D) (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
    (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ) (i : LocT B0) (c : ℕ) :
    G D.host.E D.nd.Om →* (OOf B0 i)ˣ :=
  haveI : Fact (lOf B0 i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf B0 i] (OOf B0 i) := B0.algOc _ _
  chi1N B0 C tw ps i * ((Units.map (algebraMap ℤ_[lOf B0 i] (OOf B0 i)).toMonoidHom).comp
    (cycZ (F := D.host.E) (Ω := D.nd.Om) (lOf B0 i))) ^ (-((c : ℤ) - 1))

theorem chiN_one (C : NChoice D) (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
    (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ) (i : LocT B0) : chiN B0 C tw ps i 1 = chi1N B0 C tw ps i := by
  simp [chiN]

end Loc

def gamN (D : D7) (v : PlE D.host) : G D.host.E D.nd.Om := by
  classical
  exact if h : ∃ kv : (Σ k, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = v then D.ntypes.tg h.choose.1 h.choose.2
    else if h' : ∃ γ : G D.host.E D.nd.Om, TameGenAt (D.nd.plOm.1 v) γ then h'.choose else 1

def PlGwDisj (D : D7) : Prop := ∀ k k' v v', D.naut.plGw k v = D.naut.plGw k' v' → k = k'

theorem exists_tame (D : D7) (v : PlE D.host) : ∃ γ : G D.host.E D.nd.Om, TameGenAt (D.nd.plOm.1 v) γ :=
  GlobalTheory.MemTame.exists_tameGenAt D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.plOm.2 v)

theorem gamN_gen (D : D7) (v : PlE D.host) : TameGenAt (D.nd.plOm.1 v) (gamN D v) := by
  classical
  unfold gamN
  split_ifs with h h'
  · have := D.ntypes.tg_gen h.choose.1 h.choose.2
    rwa [h.choose_spec] at this
  · exact h'.choose_spec
  · exact absurd (exists_tame D v) h'

theorem gamN_tg (D : D7) (hD : PlGwDisj D) (k : Fin 2) (v : D.nd.PlG k) : gamN D (D.naut.plGw k v) = D.ntypes.tg k v := by
  classical
  have h : ∃ kv : (Σ k, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = D.naut.plGw k v := ⟨⟨k, v⟩, rfl⟩
  unfold gamN
  rw [dif_pos h]
  have key : ∀ kv : (Σ k, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = D.naut.plGw k v → kv = ⟨k, v⟩ := by
    rintro ⟨k', v'⟩ e
    obtain rfl := hD k' k v' v e
    obtain rfl := D.naut.plGw_inj k' e
    rfl
  rw [key _ h.choose_spec]

section Build

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D)

set_option synthInstance.maxHeartbeats 400000 in

def mkX (hs : HeckeStd0 B0) (hd : FinDimV B0) (hL : MtLoc B0 (partCompl_of hs hd))
    (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
    (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i)) (hTL : ∀ i, IsLocalRing (TOf B0 i))
    (hAct : ActEx B0 (partCompl_of hs hd))
    (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
    (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
    (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
    (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
    (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
    (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
    (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
    (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
    (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i)) : LocNd (lay0 D) where
  Loc := LocT B0
  l := lOf B0
  lPrime i := ⟨D.what₂.places.resChar_prime _⟩
  j := jOf B0
  j_range i := ⟨i.2.2.2.1, i.2.2.2.2.1⟩
  mu i := D.what₂.muTw (wOf B0 i)
  w := wOf B0
  w_l _ := rfl
  mu_w _ := rfl
  w_tw i := i.2.2.2.2.2
  locs := locsC B0 (locsFin_of hs hd)
  locs_mem := locsC_mem B0 (locsFin_of hs hd)
  O := OOf B0
  algO i := B0.algOc _ _
  finO i := B0.finOc _ _
  O_adic i := B0.Oc_adic _ _
  O_complete i := B0.Oc_complete _ _
  embK i := B0.ec _ _
  embK_w i := B0.ec_w _ _
  X := XOf B0
  finX i := @Fintype.ofFinite _ (xFin_of hs hd i)
  neX := xNe_of hs hd
  T := TOf B0
  T_local := hTL
  T_sep := tSep (B := B0)
  Mt i := MtSub B0 (partCompl_of hs hd) i
  freeMt := hMF
  finMt := hMFin
  act := actC B0 (partCompl_of hs hd) hAct
  act_inj i := (hAct i).choose_spec.1
  prMt := prMtC B0 (partCompl_of hs hd) hL
  prMt_span := prMtC_span B0 (partCompl_of hs hd) hL
  prMt_lat := prMtC_latSpan B0 (partCompl_of hs hd) hL
  eig_ne := hEig
  chi := chiN B0 C tw ps
  chi_cont := hChi
  chi_def i c _ _ := by rw [chiN_one]; rfl
  s0 i := if lOf B0 i = 2 then D.host.QS.factorization 2 else max 1 (D.host.QS.factorization (lOf B0 i))
  restNLevelExponent_of_odd i hl := if_neg hl
  restNLevelExponent_of_two i hl := if_pos hl
  S i := (exceptional_places_finite D.host (lOf B0 i)).toFinset
  Q i := B0.Qw (wOf B0 i)
  SQ_split := hSQs
  SQ_disj := hSQd
  SQ_l i v hv := by
    rcases hv with hv | hv
    · rw [Set.Finite.mem_toFinset] at hv; exact hv.2
    · exact hQl _ v hv
  S_def i v := by rw [Set.Finite.mem_toFinset]; rfl
  hT := hTOf B0
  T_gen i := tGen B0 (exceptional_places_finite D.host) i
  gam0 _ v := gamN D v
  locNd_chebotarevPlace_mem _ v := (gamN_gen D v).1
  restN_tameGenerator_generates _ v _ := gamN_gen D v
  chi_ram_Q i v hv := by rw [chiN_one]; exact hRam i v hv
  Bj := BjC B0 hI
  freeBj := hBF

end Build

section Tw

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D) (hs : HeckeStd0 B0) (hd : FinDimV B0)
  (hL : MtLoc B0 (partCompl_of hs hd))
  (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hTL : ∀ i, IsLocalRing (TOf B0 i)) (hAct : ActEx B0 (partCompl_of hs hd))
  (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
  (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
  (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
  (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
  (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
  (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
  (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
  (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
  (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i))

set_option synthInstance.maxHeartbeats 400000 in

def mkT
    (hTwE : ∀ (a : LocT B0) (x : D.LL0) (y : D.ntw.O0 (C.twI (wOf B0 a))),
      algebraMap (D.ntw.O0 (C.twI (wOf B0 a))) (FractionRing (D.ntw.O0 (C.twI (wOf B0 a)))) y =
        (if C.sd (wOf B0 a) then D.ntw.emb0 (C.twI (wOf B0 a)) else D.ntw.emb0b (C.twI (wOf B0 a))) x →
      B0.ec (jOf B0 a) (wOf B0 a) (x : D.what₂.LL) = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y))
    (hOrd : ∀ a g, ∃ n : ℕ, ps a g ^ (lOf B0 a ^ n) = 1)
    (hOpen : ∀ a, IsOpen ((ps a).ker : Set (G D.host.E D.nd.Om)))
    (hAnti : ∀ a, AntiHom D.ntw.cc (ps a))
    (hRamP : ∀ a, RamExactly (ps a) (↑(B0.Qw (wOf B0 a)) : Set (HeightOneSpectrum (𝓞 D.host.E))))
    (hPl : ∀ a v, v ∈ placesOver D.host.E (lOf B0 a) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Dec (F := D.host.E) A, ps a σ = 1) :
    LocTw (mkX B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF) where
  twOf a := C.twI (wOf B0 a)
  twSide a := C.sd (wOf B0 a)
  twOf_l a := C.twI_l _
  twist₂ := tw
  twO_emb := hTwE
  psiL := ps
  psiL_ord := hOrd
  psiL_open := hOpen
  psiL_anti := hAnti
  psiL_ram := hRamP
  psiL_l := hPl
  chi_tw a := chiN_one B0 C tw ps a

end Tw

def unitsLift {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (f : Γ →* (FractionRing O)ˣ)
    (h : ∀ g, ∃ u : Oˣ, algebraMap O (FractionRing O) u = f g) : Γ →* Oˣ where
  toFun g := (h g).choose
  map_one' := by
    ext
    apply IsFractionRing.injective O (FractionRing O)
    rw [(h 1).choose_spec]
    simp
  map_mul' a b := by
    ext
    apply IsFractionRing.injective O (FractionRing O)
    rw [(h (a * b)).choose_spec, Units.val_mul, map_mul (algebraMap O (FractionRing O)), (h a).choose_spec, (h b).choose_spec]
    simp

theorem unitsLift_spec {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (f : Γ →* (FractionRing O)ˣ)
    (h : ∀ g, ∃ u : Oˣ, algebraMap O (FractionRing O) u = f g) (g : Γ) :
    algebraMap O (FractionRing O) (unitsLift f h g : O) = f g :=
  (h g).choose_spec

def iqC (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) : FractionRing (OcC X j w) →+* Qbar (D.what₂.places.resChar w) :=
  (X.Kx j w).1.val.toRingHom.comp (FractionRing.algEquiv ↥(Loc.OL (X.Kx j w)) ↥(X.Kx j w).1).toRingEquiv.toRingHom

def BigOk (pl : PlSide D) (X : CoefIn D.what₂) (big : D.what₂.places.Pl → Finset ℂ) : Prop :=
  ∀ j w, ∀ z ∈ big w, ∃ x, pl.ι w (iqC X j w x) = z

def TwEmb (C : NChoice D) (X : CoefIn D.what₂) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) : Prop :=
  ∀ j w, TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)),
    algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y =
      (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x →
    ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (twC j w y)

def TwAlgAt (C : NChoice D) (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) (f : D.ntw.O0 (C.twI w) →+* OcC X j w) : Prop :=
  haveI : Fact (D.ntw.l (C.twI w)).Prime := D.ntw.lPrime (C.twI w)
  ∀ (z : ℤ_[D.ntw.l (C.twI w)]) (z' : ℤ_[D.what₂.places.resChar w]), HEq z z' →
    f (@algebraMap _ (D.ntw.O0 (C.twI w)) _ _ (D.ntw.algO0 (C.twI w)) z) = algebraMap _ (OcC X j w) z'

def TwRdAt (C : NChoice D) (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) (f : D.ntw.O0 (C.twI w) →+* OcC X j w) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (OcC X j w) →+* Ω) (ι : FractionRing (C.Oe w) →+* Ω),
    (∀ y, τ (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) =
      ι (algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
        (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) y)))) ∧
    ∀ x : D.what₂.LL, τ (ecC X j w x) = ι (C.embW w x)

def BrAt (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) : Prop :=
  ∀ u : PlE D.host, u ∈ placesOver D.host.E (D.what₂.places.resChar w) →
    ∃ Bw : LocBridge (D.what₂.places.resChar w) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 u)) (OcC X j w),
      (∀ x, x ∈ D.nd.plOm.1 u ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef D.host.condN Bw.LL ∧
      ∀ z : OcC X j w, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) z) =
        ((Bw.toLL z : ↥Bw.LL.1) : Loc.Om (D.what₂.places.resChar w))

def GenHyp (M : MtFam D) (Q : D.what₂.places.Pl → Finset (PlE D.host)) : Prop :=
  ∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
    NG.HypOutside (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ B ∧
    ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E), GenAt D (D.what₂.places.resChar w) (Q w) v k →
      IsConjPl D.host v s.w → s.v ∉ B

theorem iqC_alg (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) (a : OcC X j w) :
    iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) a) =
      (((show ↥(Loc.OL (X.Kx j w)) from a) : ↥(X.Kx j w).1) : Loc.Om (D.what₂.places.resChar w)) :=
  congrArg Subtype.val ((FractionRing.algEquiv ↥(Loc.OL (X.Kx j w)) ↥(X.Kx j w).1).commutes a)

theorem iqC_ec (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    iqC X j w (ecC X j w x) = X.E.emb w x :=
  congrArg Subtype.val ((FractionRing.algEquiv ↥(Loc.OL (X.Kx j w)) ↥(X.Kx j w).1).apply_symm_apply
    (Formalism.BasicNotions.Examples₂.TwB.phiL (X.Kx j w) (X.E.emb w) (X.hKx j w) x))

theorem iqC_surj (X : CoefIn D.what₂) (j : ℕ) (w : D.what₂.places.Pl) (y : Loc.Om (D.what₂.places.resChar w))
    (hy : y ∈ (X.Kx j w).1) : ∃ x, iqC X j w x = y :=
  ⟨(FractionRing.algEquiv ↥(Loc.OL (X.Kx j w)) ↥(X.Kx j w).1).symm ⟨y, hy⟩,
    congrArg Subtype.val ((FractionRing.algEquiv ↥(Loc.OL (X.Kx j w)) ↥(X.Kx j w).1).apply_symm_apply ⟨y, hy⟩)⟩

def PsiInt (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) : Prop :=
  ∀ j w g, ∃ u : (OcC X j w)ˣ, algebraMap (OcC X j w) (FractionRing (OcC X j w)) u = ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL)

def psN (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0)
    (j : ℕ) (w : D.what₂.places.Pl) : G D.host.E D.nd.Om →* (OcC X j w)ˣ :=
  unitsLift ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w)

end GlobalTheory.HeckeLocN
