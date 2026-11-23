import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes

noncomputable section

namespace GlobalTheory.HeightCounting.ReadingModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain

def ofFrame {D : D7} (F : TwFrame D) : TwFrameC D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩

def toFrame {D : D7} (F : TwFrameC D) : TwFrame D :=
  ⟨F.K0, F.eO0, F.j0, F.Lw, F.eO, F.eOk, F.iCq, F.S0x⟩

theorem twTiedC_iff {D : D7} (F : TwFrameC D) : TwistFrameLowIndexCompatibility D F (lowPr D) ↔ NTwTied D (toFrame F) := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E)
  constructor
  · intro T
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN]),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (by simp [lowPr]), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (by simp [lowPr]),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd])⟩
  · intro T
    refine ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos, fun i p hp => ?_⟩
    simp only [lowPr, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | rfl | hp | hp
    · exact T.S0x_contains_two_places i
    · exact T.S0x_contains_q0_places i
    · exact T.S0x_contains_ccK_places i p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    · exact T.S0x_contains_ramified_places i p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

theorem twTiedC_of_tied {D : D7} {F : TwFrame D} (T : NTwTied D F) : TwistFrameLowIndexCompatibility D (ofFrame F) (lowPr D) :=
  (twTiedC_iff (ofFrame F)).2 T

theorem twConjAt_of_choiceC {D : D7} {C : NChoice D} (h : ChoiceC D C) : TwConjAt D C :=
  fun w hw => ⟨h.conj w hw, h.sd_conj w hw⟩

theorem choiceC_int {D : D7} {C : NChoice D} (h : ChoiceC D C) (w : D.what₂.places.Pl) (hw : TwistedAt D w) (x : D.LL0) :
    (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) ∈
        (algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w)))).range ↔
      fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) ∈
        (algebraMap (C.Oe w) (FractionRing (C.Oe w))).range := by
  rw [← h.emb_side w hw x, ← C.embW_w, h.sd_place w hw x]

section
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}

theorem ringSpec_onto (S : RingSpec D cf b0 b1 Sx T) (w : HeightOneSpectrum (𝓞 ↥D.LL0)) :
    ∃ i, ((T.l i : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal := by
  refine ⟨S.eTw.symm w, ?_⟩
  have h := (S.pl_emb (S.eTw.symm w)).1
  rwa [Equiv.apply_symm_apply] at h

theorem embedding_mem_coefficient_field (S : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (x : ↥D.LL0) : S.j0 i x ∈ (S.K0 i).1 := by
  obtain ⟨⟨y, z⟩, hyz⟩ := IsLocalization.surj (nonZeroDivisors (T.O0 i)) (T.emb0 i x)
  have hz : (z : T.O0 i) ≠ 0 := nonZeroDivisors.ne_zero z.2
  have h := (S.ringSpec_baseEmbedding_compatible i x y z hz).mp hyz
  have hz' : ((S.eO0 i z : intOf (T.l i) (S.K0 i).1) : PadicAlgCl (T.l i)) ≠ 0 := by
    intro h0
    apply hz
    exact (S.eO0 i).map_eq_zero_iff.mp (Subtype.ext h0)
  have hx : S.j0 i x = (S.eO0 i y : PadicAlgCl (T.l i)) / (S.eO0 i z : PadicAlgCl (T.l i)) := by
    rw [eq_div_iff hz', h]
  rw [hx]
  exact (S.K0 i).1.div_mem (S.eO0 i y).2.1 (S.eO0 i z).2.1

variable (hE : IsEmpty D.nd.Loc) (F : TwF T) (S : RingSpec D cf b0 b1 Sx T)
  (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
  (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex)

def withRings : D7 := setTw D (T.ntw hE F (TwL.empty T)) ex h0 th S.br S.br_ind

def chiData : NChiData (withRings hE F S ex h0 th) :=
  ⟨S.mu0H, S.etaH, S.delH, fun a => hE.elim a, fun _ a => PEmpty.elim a, S.embO⟩

theorem chiTied : NormalizedCharacterCompatibility (withRings hE F S ex h0 th) (chiData hE F S ex h0 th) :=
  ⟨fun a => hE.elim a, S.del_fix, S.delta, S.chi1, S.ringSpec_sidedEmbedding_fixedField, S.etaT_unr, S.etaT_inf, fun _ a => PEmpty.elim a⟩

def charFrame : CharFrame (withRings hE F S ex h0 th) :=
  ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩

theorem deltaRead : DeltaRead (withRings hE F S ex h0 th) (charFrame hE F S ex h0 th) := S.deltaRead

def frameC : TwFrameC (withRings hE F S ex h0 th) :=
  ⟨S.K0, S.eO0, S.j0, S.Lw, S.eO, S.eOk, S.iCq, fun _ => Sx⟩

theorem tiedC (low : Finset ℕ) (hlow : ∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx)
    (hconj : ∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx)
    (hk : ∀ (i : (withRings hE F S ex h0 th).ntw.Tw) j b k P, P ∉ (withRings hE F S ex h0 th).ntw.S0 i → ∃ s : Multiset (FractionRing ((withRings hE F S ex h0 th).ntw.O i)),
      (LinearMap.charpoly ((withRings hE F S ex h0 th).ntw.hk i j b k P)).map
        (algebraMap ((withRings hE F S ex h0 th).ntw.O i) (FractionRing ((withRings hE F S ex h0 th).ntw.O i))) =
        (s.map fun a => Polynomial.X - Polynomial.C a).prod)
    (hB : ∀ i j b, LinearMap.range ((withRings hE F S ex h0 th).nexp.embB i j b) =
      (withRings hE F S ex h0 th).nexp.Bsup i j b ⊓
        (NForms.V0 (withRings hE F S ex h0 th) i j b).restrictScalars ((withRings hE F S ex h0 th).ntw.O i))
    (hs : ∀ i (s s' : F.Sig i), F.jS i s = F.jS i s' → F.side i s = F.side i s' →
      (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → F.hEig i s k P = F.hEig i s' k P) → s = s') :
    TwistFrameLowIndexCompatibility (withRings hE F S ex h0 th) (frameC hE F S ex h0 th) low :=
  ⟨fun i => ⟨S.eTw i, S.pl_emb i⟩, S.ringSpec_baseIntegersEquiv_algebraMap, S.ringSpec_baseEmbedding_compatible, S.eO_alg, S.eOk_alg, S.mu_g, hk, S.ringSpec_excludedPlaces_eq, fun _ => hconj, hB, hs,
    fun _ a => PEmpty.elim a, fun _ => hlow⟩

end

end GlobalTheory.HeightCounting.ReadingModel

end
