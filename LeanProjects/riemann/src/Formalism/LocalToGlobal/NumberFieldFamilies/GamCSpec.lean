import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCTypTame

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

def ActSpec (hC : PartCompl B) (i : LocT B) (a : TOf B i →ₐ[OOf B i] Module.End (OOf B i) (MtSub B hC i)) : Prop :=
  Function.Injective a ∧ ∀ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k → ∀ m : MtSub B hC i,
    (((a (hTOf B i v k) m : MtSub B hC i) : partOf B i) : B.V (jOf B i) (wOf B i)) =
      B.hK (jOf B i) (wOf B i) v k ((m : partOf B i) : B.V (jOf B i) (wOf B i))

def ActEx (hC : PartCompl B) : Prop := ∀ i, ∃ a, ActSpec B hC i a

def actC (hC : PartCompl B) (hA : ActEx B hC) (i : LocT B) :
    TOf B i →ₐ[OOf B i] Module.End (OOf B i) (MtSub B hC i) := (hA i).choose

def OsInt : Prop := ∀ j w (y : what₂.O), B.ec j w (what₂.OtoLL y) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range

def sOfC (hI : OsInt B) (i : LocT B) : what₂.O →+* OOf B i :=
  (Formalism.L2.fracRangeEquiv (OOf B i)).symm.toRingHom.comp
    (((B.ec (jOf B i) (wOf B i)).comp what₂.OtoLL).codRestrict _ (hI _ _))

def bjRel (hI : OsInt B) (i : LocT B) : Submodule (OOf B i) ((what₂.MjLat (jOf B i)).gen → OOf B i) :=
  Submodule.span (OOf B i) ((fun r => (sOfC B hI i) ∘ r) '' Formalism.L2.latRel (what₂.MjLat (jOf B i)))

abbrev BjC (hI : OsInt B) (i : LocT B) : Type := ((what₂.MjLat (jOf B i)).gen → OOf B i) ⧸ bjRel B hI i

def chiC (chi1 : ∀ i : LocT B, G H.E (OmC H) →* (OOf B i)ˣ) (i : LocT B) (c : ℕ) : G H.E (OmC H) →* (OOf B i)ˣ :=
  haveI : Fact (lOf B i).Prime := ⟨what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf B i] (OOf B i) := B.algOc _ _
  chi1 i * ((Units.map (algebraMap ℤ_[lOf B i] (OOf B i)).toMonoidHom).comp (cycZ H.E (OmC H) (lOf B i))) ^ (-((c : ℤ) - 1))

theorem chiC_one (chi1 : ∀ i : LocT B, G H.E (OmC H) →* (OOf B i)ˣ) (i : LocT B) : chiC B chi1 i 1 = chi1 i := by
  simp [chiC]

def finOf {X : Type} (hX : Finite X) (Z : Set X) : Finset X := by
  classical
  exact @Finset.filter _ (· ∈ Z) _ (@Finset.univ _ (@Fintype.ofFinite _ hX))

theorem tGen (hS : ∀ l, (exceptionalPlaces H l).Finite) (i : LocT B) :
    Algebra.adjoin (OOf B i) {f : XOf B i → OOf B i | ∃ v k, IsSplitPl H v ∧ v ∉ placesOver H.E (lOf B i) ∧
      v ∉ (hS (lOf B i)).toFinset ∧ v ∉ B.Qw (wOf B i) ∧ 1 ≤ k ∧ k ≤ R.nV ∧ f = (hTOf B i v k : XOf B i → OOf B i)} = TOf B i := by
  unfold TOf
  congr 1
  ext f
  simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩
    have hg : GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k := ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨v, k, hg, by simp [hTOf, dif_pos hg]⟩
  · rintro ⟨v, k, hg, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
    exact ⟨v, k, h1, h2, h3, h4, h5, h6, by simp [hTOf, dif_pos (show GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k from ⟨h1, h2, h3, h4, h5, h6⟩)]⟩

def TgEx {R : Ranks} (H : Host R) (h : PlOverEx H) : Prop :=
  ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 H.E)), v ∈ placesOver H.E (H.g k) →
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    ∃ σ : G H.E (OmC H), Formalism.L2.Fam.NPCTyp.TgSpec ((plOmC H h).1 v) (H.g k) σ

def gamC {R : Ranks} (H : Host R) (h : PlOverEx H) (v : HeightOneSpectrum (𝓞 H.E)) : G H.E (OmC H) :=
  Formalism.L2.Fam.NPCTyp.gamG H (plOmC H h) (gamW H h) v

theorem gamC_spec {R : Ranks} (H : Host R) (h : PlOverEx H) (ht : TameEx H h) (hg : TgEx H h) (v : HeightOneSpectrum (𝓞 H.E)) :
    TameGenAt ((plOmC H h).1 v) (gamC H h v) := by
  unfold gamC Formalism.L2.Fam.NPCTyp.gamG
  split_ifs with h0 h1
  · haveI : Fact (H.g 0).Prime := ⟨H.g_prime 0⟩
    exact (Classical.epsilon_spec (hg 0 v h0)).1
  · haveI : Fact (H.g 1).Prime := ⟨H.g_prime 1⟩
    exact (Classical.epsilon_spec (hg 1 v h1)).1
  · exact gamW_gen H h ht v

end Gen

section Assemble

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R) (B : LocBase0 H what₂)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def ndC (h : PlOverEx H) (ht : TameEx H h)
    (hSha : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldatC H h p) (e : ℤ) = (n : ℕ∞) → what₂.shaLen p e = (n : ℚ))
    (hF : LocsFin B) (hXfin : ∀ i, Finite (XOf B i)) (hXne : ∀ i, Nonempty (XOf B i))
    (hTL : ∀ i, IsLocalRing (TOf B i))
    (hTS : ∀ i (x y : XOf B i), x ≠ y → ∃ f ∈ TOf B i, (f : XOf B i → OOf B i) x ≠ (f : XOf B i → OOf B i) y)
    (hC : PartCompl B) (hL : MtLoc B hC) (hMF : ∀ i, Module.Free (OOf B i) (MtSub B hC i))
    (hMFin : ∀ i, Module.Finite (OOf B i) (MtSub B hC i)) (hAct : ActEx B hC)
    (hPS : ∀ i, Submodule.span (FractionRing (OOf B i)) (Set.range (prMtC B hC hL i)) = ⊤)
    (hPL : ∀ i, Submodule.span (OOf B i) (prMtC B hC hL i '' latL B i) =
      LinearMap.range (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1))
    (hEig : ∀ i x, heckeEig (TOf B i) (actC B hC hAct i) x ≠ ⊥)
    (chi1 : ∀ i : LocT B, G H.E (OmC H) →* (OOf B i)ˣ)
    (hChiC : ∀ i c, Continuous (fun g => ((chiC B chi1 i c g : (OOf B i)ˣ) : OOf B i)))
    (Zs Zgs : ∀ i : LocT B, Set (XOf B i))
    (hS : ∀ l, (exceptionalPlaces H l).Finite) (hTg : TgEx H h)
    (hSQs : ∀ i v, v ∈ (hS (lOf B i)).toFinset ∨ v ∈ B.Qw (wOf B i) → IsSplitPl H v)
    (hSQd : ∀ i, Disjoint (hS (lOf B i)).toFinset (B.Qw (wOf B i)))
    (hQl : ∀ w v, v ∈ B.Qw w → v ∉ placesOver H.E (what₂.places.resChar w))
    (hRam : ∀ i, ∀ v ∈ B.Qw (wOf B i), ∃ g ∈ Ine (F := H.E) ((plOmC H h).1 v), chi1 i g ≠ 1)
    (hI : OsInt B) (hBF : ∀ i, Module.Free (OOf B i) (BjC B hI i))
    (thJ thJP : ∀ i, Submodule (OOf B i) (BjC B hI i))
    (hGs : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (hPG : PlGFin H) (hPGc : ∀ k, Nat.card (PlGC H k) = R.f)
    (lab : ∀ k, what₂.FT → PlGC H k → Polynomial (ZMod (H.g k)))
    (hLab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r)
    (chiT : ∀ k, PlGC H k → Fin R.m → (ZMod (H.g k))ˣ)
    (hG0 : what₂.restRowsFiniteGroupCard = ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f) :
    NData R H what₂ where
  Om := OmC H
  plOm := plOmC H h
  ldat p _ := ldatC H h p
  sha_eq := hSha
  Loc := LocT B
  l := lOf B
  lPrime i := ⟨what₂.places.resChar_prime _⟩
  j := jOf B
  j_range i := ⟨i.2.2.2.1, i.2.2.2.2.1⟩
  mu i := what₂.muTw (wOf B i)
  w := wOf B
  w_l _ := rfl
  mu_w _ := rfl
  w_tw i := i.2.2.2.2.2
  locs := locsC B hF
  locs_mem := locsC_mem B hF
  O := OOf B
  algO i := B.algOc _ _
  finO i := B.finOc _ _
  O_adic i := B.Oc_adic _ _
  O_complete i := B.Oc_complete _ _
  embK i := B.ec _ _
  embK_w i := B.ec_w _ _
  X := XOf B
  finX i := @Fintype.ofFinite _ (hXfin i)
  neX := hXne
  T := TOf B
  T_local := hTL
  T_sep := hTS
  Mt i := MtSub B hC i
  freeMt := hMF
  finMt := hMFin
  act := actC B hC hAct
  act_inj i := (hAct i).choose_spec.1
  prMt := prMtC B hC hL
  prMt_span := hPS
  prMt_lat := hPL
  eig_ne := hEig
  chi := chiC B chi1
  chi_cont := hChiC
  chi_def i c _ _ := by rw [chiC_one]; rfl
  Z i := finOf (hXfin i) (Zs i)
  Zgood i := finOf (hXfin i) (Zgs i)
  s0 i := if lOf B i = 2 then H.QS.factorization 2 else max 1 (H.QS.factorization (lOf B i))
  restNLevelExponent_of_odd i hl := if_neg hl
  restNLevelExponent_of_two i hl := if_pos hl
  S i := (hS (lOf B i)).toFinset
  Q i := B.Qw (wOf B i)
  SQ_split := hSQs
  SQ_disj := hSQd
  SQ_l i v hv := by
    rcases hv with hv | hv
    · rw [Set.Finite.mem_toFinset] at hv; exact hv.2
    · exact hQl _ v hv
  S_def i v := by rw [Set.Finite.mem_toFinset]; rfl
  hT := hTOf B
  T_gen i := tGen B hS i
  gam0 _ v := gamC H h v
  locNd_chebotarevPlace_mem _ v := (gamC_spec H h ht hTg v).1
  restN_tameGenerator_generates _ v _ := gamC_spec H h ht hTg v
  chi_ram_Q i v hv := by rw [chiC_one]; exact hRam i v hv
  Bj := BjC B hI
  freeBj := hBF
  g_split := hGs
  PlG := PlGC H
  finPlG k := @Fintype.ofFinite _ (hPG k)
  card_PlG k := by rw [← hPGc k]; exact (@Nat.card_eq_fintype_card _ (@Fintype.ofFinite _ (hPG k))).symm
  lab := lab
  lab_monic := hLab
  chiT := chiT
  restN_card_levelGroup_eq := hG0

end Assemble

end Formalism.L2.Fam.NPC
