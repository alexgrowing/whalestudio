import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalToHecke

namespace GlobalTheory.Mem.Top.TwChar

theorem torsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] torsionFree_field

section Roots

variable {O : Type} [CommRing O] [IsDomain O] {n : ℕ}

def rootIso [NeZero n] {ζ : O} (h : IsPrimitiveRoot ζ n) : rootsOfUnity n O ≃* rootsOfUnity n ℂ :=
  mulEquivOfCyclicCardEq
    (h.card_rootsOfUnity.trans (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).card_rootsOfUnity.symm)

variable {Γ : Type} [Group Γ]

def cxChar (ι : rootsOfUnity n O ≃* rootsOfUnity n ℂ) (ψ : Γ →* Oˣ) (h : ∀ g, ψ g ∈ rootsOfUnity n O) : Γ →* ℂˣ :=
  (rootsOfUnity n ℂ).subtype.comp (ι.toMonoidHom.comp (ψ.codRestrict _ h))

variable (ι : rootsOfUnity n O ≃* rootsOfUnity n ℂ) (ψ : Γ →* Oˣ) (h : ∀ g, ψ g ∈ rootsOfUnity n O)

omit [IsDomain O] in
theorem cxChar_apply (g : Γ) : cxChar ι ψ h g = (ι ⟨ψ g, h g⟩ : ℂˣ) := rfl

omit [IsDomain O] in
theorem cxChar_eq_one (g : Γ) : cxChar ι ψ h g = 1 ↔ ψ g = 1 := by
  rw [cxChar_apply, OneMemClass.coe_eq_one, map_eq_one_iff _ ι.injective, Subtype.ext_iff]
  rfl

omit [IsDomain O] in
theorem cxChar_pow (g : Γ) : cxChar ι ψ h g ^ n = 1 := (ι ⟨ψ g, h g⟩).2

theorem exists_exponent [NeZero n] {ζ : O} (hζ : IsPrimitiveRoot ζ n) {L M : Type} [Field L] [Field M] (ε : L →+* ℂ)
    (hL : ∀ z : ℂ, z ^ n = 1 → ∃ x, ε x = z) (e : L →+* M) (j : O →+* M) (hj : Function.Injective j) :
    ∃ a : ℕ, a.Coprime n ∧ ∀ (u : rootsOfUnity n O) (x : L), ε x = ((ι u : ℂˣ) : ℂ) → e x = j (((u : Oˣ) ^ a : Oˣ) : O) := by
  let u0 : rootsOfUnity n O := hζ.toRootsOfUnity
  have h0 : IsPrimitiveRoot u0 n := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
    exact hζ
  have h1 : IsPrimitiveRoot (((ι u0 : rootsOfUnity n ℂ) : ℂˣ) : ℂ) n := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
    exact h0.map_of_injective ι.injective
  obtain ⟨x0, hx0⟩ := hL _ h1.pow_eq_one
  have h2 : IsPrimitiveRoot (e x0) n := (IsPrimitiveRoot.of_map_of_injective (hx0 ▸ h1) ε.injective).map_of_injective e.injective
  have h3 : IsPrimitiveRoot (j ζ) n := hζ.map_of_injective hj
  obtain ⟨a, -, ha⟩ := h3.eq_pow_of_pow_eq_one h2.pow_eq_one
  refine ⟨a, (h3.pow_iff_coprime (NeZero.pos n) a).1 (ha ▸ h2), fun u x hx => ?_⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((u : Oˣ) : O)) (by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one])
  have hu : u = u0 ^ b := Subtype.ext (Units.ext hb.symm)
  have hx' : x = x0 ^ b := ε.injective (by rw [hx, map_pow, hx0, hu, map_pow]; rfl)
  rw [hx', map_pow, ← ha, Units.val_pow_eq_pow_val, ← hb, map_pow, map_pow, ← pow_mul, ← pow_mul, mul_comm]

end Roots

theorem not_mem_sq_of_ramificationIdx {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (he : v.asIdeal.ramificationIdx ℤ = 1) :
    ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal hb] at he
  intro h
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem isPsi_of_isHeckeOf {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]
    {cc : Ω ≃+* Ω} (hcc : IsCMConjOm H.E Ω cc) {art : Ideles H.E →* Gab H.E Ω} (ha : IsGlobalArtin art)
    {r : G H.E Ω →* ℂˣ} {χ : HChar H.E} (h : IsHeckeOf art r χ) {l k : ℕ} (hl : l.Prime) {Q : Finset (PlE H)} {S : Set ℕ}
    (hanti : AntiHom cc r) (hord : ∀ g, r g ^ l ^ k = 1) (hram : RamExactly r (↑Q : Set (PlE H)))
    (hdec : ∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, r σ = 1)
    (hQ : ∀ P ∈ Q, IsSplitPl H P ∧ P.asIdeal.inertiaDeg ℤ = 1 ∧ eWL H.E P = 1)
    (hS : ∀ P ∈ Q, ∀ p ∈ S, p.Prime → P ∉ placesOver H.E p) :
    IsPsi (H := H) l Q χ ∧ χ.OrderDvd (l ^ k) ∧ Chr.IsTwist H S χ := by
  have ho := h.orderDvd hord
  have hatl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1 := fun v hv x =>
    let ⟨A, hA⟩ := exists_isPlaceOver Ω v
    h.loc_eq_one ha hA (hdec v hv A hA) x
  have htame : ∀ v, χ.TameAt v := fun v => by
    by_cases hv : OverP H l v
    · exact fun x _ _ => hatl v hv x
    · exact tameAt_of_orderDvd hl ho hv
  have hunr : ∀ v, χ.UnrAt v ↔ v ∉ Q := fun v => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    rw [h.unr_iff ha hA, ← Finset.mem_coe, ← hram v A hA]
    push Not
    rfl
  have htriv : χ.TrivOn H.F := by
    obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
    obtain ⟨j, hj⟩ := hcc.1
    have h1 : ∀ x : H.E, cc (algebraMap H.E Ω x) = algebraMap H.E Ω (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (H.conjE_apply (j.comp (algebraMap H.E Ω)) x).symm
    have h2 : ∀ x, cc (cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have := hcm.cplx
    exact h.trivOn c hcm.rank hcm.ne (fun x => (algebraMap H.E Ω).injective (by rw [← h1, ← h1, h2])) hr cc h1 h2 ha hanti
      (pow_pos hl.pos k) ho htame
  refine ⟨⟨⟨k, ho⟩, htriv, htame, hunr, hatl, fun v hv => (hQ v hv).1⟩, ho, ⟨_, pow_pos hl.pos k, ho⟩, htriv, htame,
    fun v hv => ?_⟩
  have hvQ : v ∈ Q := by_contra fun hn => hv ((hunr v).2 hn)
  obtain ⟨h1, h2, h3⟩ := hQ v hvQ
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 h2
  exact ⟨h1, hp, not_mem_sq_of_ramificationIdx hp v (Ideal.absNorm_mem _) h3,
    fun hm => hS v hvQ _ hm hp (Ideal.absNorm_mem _)⟩

section Pick

variable {D : D7} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {A Q : Finset (PlE D.host)} {k : ℕ}
  {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}

abbrev RootIso (D : D7) (i : D.ntw.Tw) (k : ℕ) : Type :=
  rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k) ≃* rootsOfUnity (D.ntw.l i ^ k) ℂ

def rootIsoAt (D : D7) (i : D.ntw.Tw) (k : ℕ) : RootIso D i k :=
  haveI : NeZero (D.ntw.l i ^ k) := ⟨pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero⟩
  rootIso (D.ntw.zk_prim i k)

theorem pick_mem (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (g : G D.host.E D.nd.Om) :
    ψ.comp (D.ntw.art i Q) g ∈ rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k) :=
  (Subgroup.zpowers_le.2 (Units.ext (D.ntw.zk_prim i k).pow_eq_one)) (h.2.2.2.2.2.1 g)

def pickGal (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) : G D.host.E D.nd.Om →* ℂˣ :=
  cxChar ι (ψ.comp (D.ntw.art i Q)) (pick_mem h)

theorem isOpen_ker_pickGal (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) :
    IsOpen ((pickGal h ι).ker : Set (G D.host.E D.nd.Om)) := by
  convert h.2.2.2.1 using 1
  ext g
  exact cxChar_eq_one _ _ _ g

def pickChar (ha : IsGlobalArtin art) (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) : HChar D.host.E :=
  heckeOf ha (pickGal h ι) (isOpen_ker_pickGal h ι)

def ReadsPick (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ι : RootIso D i k) (χ : HChar D.host.E) : Prop :=
  ∀ (x : Ideles D.host.E) (σ : G D.host.E D.nd.Om), art x = toAb D.host.E D.nd.Om σ →
    ∃ u : rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k), (u : (D.ntw.Ok i k)ˣ) = ψ (D.ntw.art i Q σ) ∧ χ.1 x = ι u

def FrobPick (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ι : RootIso D i k) (χ : HChar D.host.E) : Prop :=
  ∀ v, v ∉ Q → ∀ A' : ValuationSubring D.nd.Om, IsPlaceOver A' v → ∀ σ : G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) A' (normV v) σ →
    ∃ u : rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k), (u : (D.ntw.Ok i k)ˣ) = ψ (D.ntw.art i Q σ) ∧
      χ.val v = ((ι u : rootsOfUnity (D.ntw.l i ^ k) ℂ) : ℂˣ)⁻¹

theorem pickChar_spec (ha : IsGlobalArtin art) (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) {S : Set ℕ}
    (hS : ∀ p ∈ S, p.Prime → placesOver D.host.E p ⊆ ↑A) :
    ReadsPick art i Q k ψ ι (pickChar ha h ι) ∧ FrobPick i Q k ψ ι (pickChar ha h ι) ∧
      IsPsi (H := D.host) (D.ntw.l i) Q (pickChar ha h ι) ∧ (pickChar ha h ι).OrderDvd (D.ntw.l i ^ k) ∧
      Chr.IsTwist D.host S (pickChar ha h ι) := by
  classical
  have hH := isHeckeOf_heckeOf ha (pickGal h ι) (isOpen_ker_pickGal h ι)
  have key := isPsi_of_isHeckeOf (S := S) (Q := Q) (k := k) D.ntw.cc_cm ha hH (D.ntw.lPrime i).out
    (fun g g' hg => by
      rw [eq_inv_iff_mul_eq_one, ← map_mul, pickGal, cxChar_eq_one, map_mul, h.2.2.2.2.1 g g' hg, inv_mul_cancel])
    (cxChar_pow _ _ _)
    (fun v A' hA' => by
      rw [← h.2.2.2.2.2.2.1 v A' hA']
      exact exists_congr fun σ => and_congr Iff.rfl (not_congr (cxChar_eq_one _ _ _ σ)))
    (fun v hv A' hA' σ hσ => (cxChar_eq_one _ _ _ σ).2 (h.2.2.2.2.2.2.2 v hv A' hA' σ hσ)) h.1
    (fun P hP p hp hp' hm => Finset.disjoint_left.1 h.2.1 hP (by
      simp only [Finset.mem_union]
      exact Or.inr (hS p hp hp' hm)))
  exact ⟨fun x σ e => ⟨⟨_, pick_mem h σ⟩, rfl, hH x σ e⟩,
    fun v hv A' hA' σ hσ => ⟨⟨_, pick_mem h σ⟩, rfl, hH.val_eq ha ((key.1.ram v).2 hv) hA' hσ⟩, key⟩

theorem pick_not_over (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) {v : PlE D.host} (hv : v ∈ Q) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ v ∉ A := by
  classical
  have := Finset.disjoint_left.1 h.2.1 hv
  simp only [Finset.mem_union, not_or] at this
  exact ⟨fun hm => this.1 (D.ntw.twistExcludedPlaces_contains_residueChar i hm), this.2⟩

end Pick

section Enlarge

variable {B B' : Base}

def incl (h : Enl B B') : B.LL →+* B'.LL :=
  (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
    (B.embLL.codRestrict B'.embLL.fieldRange fun x => h.2.2.2 ⟨x, rfl⟩)

theorem embLL_incl (h : Enl B B') (x : B.LL) : B'.embLL (incl h x) = B.embLL x :=
  congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, h.2.2.2 ⟨x, rfl⟩⟩)

theorem incl_star (h : Enl B B') (x : B.LL) : incl h (star x) = star (incl h x) :=
  B'.embLL.injective (by rw [B'.starLL_cx, embLL_incl, embLL_incl, B.starLL_cx])

def plUnder (h : Enl B B') (w : B'.places.Pl) : B.places.Pl where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingHom (incl h)) (w : HeightOneSpectrum (𝓞 B'.LL)).asIdeal
  isPrime := haveI := (w : HeightOneSpectrum (𝓞 B'.LL)).isPrime; Ideal.comap_isPrime _ _
  ne_bot := fun e => by
    have h1 : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) ∈
        Ideal.comap (RingOfIntegers.mapRingHom (incl h)) (w : HeightOneSpectrum (𝓞 B'.LL)).asIdeal := by
      rw [Ideal.mem_comap, map_natCast]
      exact Examples₂.PlacesToy.resCharW_mem w
    rw [e, Ideal.mem_bot] at h1
    exact (Examples₂.PlacesToy.resCharW_prime w).ne_zero (by exact_mod_cast h1)

theorem mem_plUnder (h : Enl B B') (w : B'.places.Pl) (x : 𝓞 B.LL) :
    x ∈ HeightOneSpectrum.asIdeal (plUnder h w) ↔ RingOfIntegers.mapRingHom (incl h) x ∈ HeightOneSpectrum.asIdeal w := Iff.rfl

theorem resChar_plUnder (h : Enl B B') (w : B'.places.Pl) : B.places.resChar (plUnder h w) = B'.places.resChar w :=
  Examples₂.PlacesToy.prime_mem_unique (plUnder h w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) (by rw [mem_plUnder, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)

theorem plUnder_conj (h : Enl B B') (w : B'.places.Pl) : plUnder h (B'.places.conj w) = B.places.conj (plUnder h w) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have h1 := Examples₂.PlacesToy.mem_conjW_pow (K := B'.LL) w (RingOfIntegers.mapRingHom (incl h) x) 1
  have h2 := Examples₂.PlacesToy.mem_conjW_pow (K := B.LL) (plUnder h w) x 1
  simp only [pow_one] at h1 h2
  have e : RingOfIntegers.mapRingHom (incl h) (Examples₂.PlacesToy.starO x) =
      Examples₂.PlacesToy.starO (RingOfIntegers.mapRingHom (incl h) x) := RingOfIntegers.ext (incl_star h x)
  exact h1.trans (by rw [← e]; exact h2.symm)

theorem plUnder_surjective (h : Enl B B') : Function.Surjective (plUnder h) := fun v => by
  letI : Algebra B.LL B'.LL := (incl h).toAlgebra
  have := (v : HeightOneSpectrum (𝓞 B.LL)).isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver (v : HeightOneSpectrum (𝓞 B.LL)).asIdeal (S := 𝓞 B'.LL)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot (v : HeightOneSpectrum (𝓞 B.LL)).ne_bot Q⟩,
    HeightOneSpectrum.ext hl.over.symm⟩

def tr {P P' : Pre} (e : P' = P) (F : Pre → Type) (x : F P) : F P' := cast (congrArg F e.symm) x

theorem tr_heq {P P' : Pre} (e : P' = P) (F : Pre → Type) (x : F P) : HEq (tr e F x) x := cast_heq _ _

def TwProp (P : Pre) (l k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 P.host.E))) (χ : HChar P.host.E) : Prop :=
  IsPsi (H := P.host) l Q χ ∧ χ.OrderDvd (l ^ k) ∧ Chr.IsTwist P.host (offSet P) χ ∧ ∀ v ∈ Q, ((l : ℕ) : 𝓞 P.host.E) ∉ v.asIdeal

theorem TwProp.tr {P P' : Pre} (e : P' = P) {l k : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 P.host.E))} {χ : HChar P.host.E}
    (h : TwProp P l k Q χ) :
    TwProp P' l k (tr e (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) Q) (tr e (fun P => HChar P.host.E) χ) := by
  subst e
  exact h

theorem twProp (T : TwDat B) (w : B.places.Pl) : TwProp B.toPre (B.places.resChar w) (T.k w) (T.Q w) (T.psi w) :=
  ⟨T.psi_is w, T.psi_ord w, T.psi_tw w, T.Q_l w⟩

theorem tr_one {P P' : Pre} (e : P' = P) : tr e (fun P => HChar P.host.E) 1 = 1 := by
  subst e
  rfl

def pull (h : Enl B B') (T : TwDat B) : TwDat B' where
  pl := T.pl
  Q w := tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) (T.Q (plUnder h w))
  k w := T.k (plUnder h w)
  psi w := tr h.1 (fun P => HChar P.host.E) (T.psi (plUnder h w))
  psi_is w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).1
  psi_ord w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).2.1
  psi_tw w := ((twProp T (plUnder h w)).tr h.1).2.2.1
  Q_l w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).2.2.2
  off w hw := by
    obtain ⟨h1, h2⟩ := T.off (plUnder h w) (by rwa [resChar_plUnder])
    exact ⟨by rw [h1, tr_one], h2⟩
  conj w := by
    rw [plUnder_conj, (T.conj _).1, (T.conj _).2]
    exact ⟨rfl, rfl⟩

theorem set_pull (h : Enl B B') (T : TwDat B) (f : Fr B.toPre) :
    HEq ((pull h T).set (tr h.1 Fr f)) (T.set f) := by
  have key : ∀ (P : Pre) (e : P = B.toPre) (a : B'.places.Pl → HChar P.host.E),
      (∀ w, a w = (if B'.places.resChar w = P.host.pde then (tr e Fr f).del' else (tr e Fr f).del) *
        tr e (fun P => HChar P.host.E) (T.psi (plUnder h w))) →
      HEq ({1, (tr e Fr f).del, (tr e Fr f).del'} ∪ Set.range a : Set (HChar P.host.E)) (T.set f) := by
    intro P e a ha
    subst e
    have : a = T.xiTw f ∘ plUnder h := funext fun w => by
      rw [ha, ← resChar_plUnder h]
      rfl
    rw [this, (plUnder_surjective h).range_comp]
    rfl
  exact key B'.toPre h.1 _ fun _ => rfl

theorem avoids_pull (h : Enl B B') {T : TwDat B} {Av : ℕ → Finset ℕ} (hA : T.Avoids Av) : (pull h T).Avoids Av := by
  have key : ∀ (P : Pre) (e : P = B.toPre) (Q : Finset (HeightOneSpectrum (𝓞 B.host.E))) (s : Finset ℕ),
      (∀ v ∈ Q, Ideal.absNorm v.asIdeal ∉ s) →
      ∀ v ∈ tr e (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) Q, Ideal.absNorm v.asIdeal ∉ s := by
    intro P e Q s hs
    subst e
    exact hs
  intro w
  rw [← resChar_plUnder h]
  exact key _ h.1 _ _ (hA (plUnder h w))

theorem exists_enl_roots (T : TwDat B) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, Enl B B' ∧ (∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z) ∧
      ∀ (w : B.places.Pl) (z : ℂ), z ^ B.places.resChar w ^ T.k w = 1 → ∃ x : B'.LL, B'.embLL x = z := by
  classical
  have hpos : ∀ w, 0 < B.places.resChar w ^ T.k w := fun w => pow_pos (B.places.resChar_prime w).pos _
  obtain ⟨B', h, hS'⟩ := BaseEnl.exists_enl B (S ∪ (TwFin.finite_pl B T.pl).toFinset.biUnion fun w =>
    Polynomial.nthRootsFinset (B.places.resChar w ^ T.k w) (1 : ℂ)) (by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact hS z hz
      · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hz
        rw [Polynomial.mem_nthRootsFinset (hpos w)] at hw
        exact IsAlgebraic.of_pow (hpos w) (hw ▸ isAlgebraic_one))
  refine ⟨B', h, fun z hz => hS' z (Finset.mem_union_left _ hz), fun w z hz => ?_⟩
  by_cases hw : B.places.resChar w ∈ T.pl
  · exact hS' z (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨w, (Set.Finite.mem_toFinset _).2 hw, (Polynomial.mem_nthRootsFinset (hpos w) _).2 hz⟩))
  · rw [(T.off w hw).2, pow_zero, pow_one] at hz
    exact ⟨1, by rw [map_one, hz]⟩

end Enlarge

section Data

def ofFamily (B : Base) (pl : Finset ℕ) {I : Type} (s : B.places.Pl → I) (Q : I → Finset (HeightOneSpectrum (𝓞 B.host.E)))
    (k : I → ℕ) (χ : I → HChar B.host.E)
    (h : ∀ w, B.places.resChar w ∈ pl → TwProp B.toPre (B.places.resChar w) (k (s w)) (Q (s w)) (χ (s w)))
    (hs : ∀ w, B.places.resChar w ∈ pl → s (B.places.conj w) = s w) : TwDat B where
  pl := pl
  Q w := if B.places.resChar w ∈ pl then Q (s w) else ∅
  k w := if B.places.resChar w ∈ pl then k (s w) else 0
  psi w := if B.places.resChar w ∈ pl then χ (s w) else 1
  psi_is w := by
    split_ifs with hw
    exacts [(h w hw).1, isPsi_one _]
  psi_ord w := by
    split_ifs with hw
    exacts [(h w hw).2.1, one_pow _]
  psi_tw w := by
    split_ifs with hw
    exacts [(h w hw).2.2.1, Chr.isTwist_one _ _]
  Q_l w := by
    split_ifs with hw
    exacts [(h w hw).2.2.2, fun _ h => absurd h (Finset.notMem_empty _)]
  off w hw := ⟨if_neg hw, if_neg hw⟩
  conj w := by
    rw [TwFin.resChar_conj]
    split_ifs with hw
    exacts [by rw [hs w hw]; exact ⟨rfl, rfl⟩, ⟨rfl, rfl⟩]

open Classical in

def avoidPlaces (P : Pre) (s : Finset ℕ) : Finset (HeightOneSpectrum (𝓞 P.host.E)) :=
  (((finite_offSet P).union s.finite_toSet).inter_of_left {p | p.Prime}).toFinset.attach.biUnion fun p =>
    (placesOver_finite_av P.host.E p.1 (((Set.Finite.mem_toFinset _).1 p.2).2.ne_zero)).toFinset

theorem subset_avoidPlaces (P : Pre) (s : Finset ℕ) {p : ℕ} (h : p ∈ offSet P ∨ p ∈ s) (hp : p.Prime) :
    placesOver P.host.E p ⊆ ↑(avoidPlaces P s) := fun v hv => by
  classical
  rw [Finset.mem_coe, avoidPlaces, Finset.mem_biUnion]
  exact ⟨⟨p, (Set.Finite.mem_toFinset _).2 ⟨h, hp⟩⟩, Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).2 hv⟩

end Data

open Classical in

def settingChar {D : D7} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} (ha : IsGlobalArtin art)
    (A Q : D.ntw.Tw → Finset (PlE D.host)) (k : D.ntw.Tw → ℕ) (ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ)
    (ι : ∀ i, RootIso D i (k i)) (i : D.ntw.Tw) : HChar D.host.E :=
  if h : BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) then pickChar ha h (ι i) else 1

open Classical in

def ofFamilyOn (B : Base) (pl : Finset ℕ) (Wt : Set B.places.Pl) (hsub : ∀ w ∈ Wt, B.places.resChar w ∈ pl)
    (hc : ∀ w, B.places.conj w ∈ Wt ↔ w ∈ Wt) {I : Type} (s : B.places.Pl → I)
    (Q : I → Finset (HeightOneSpectrum (𝓞 B.host.E))) (k : I → ℕ) (χ : I → HChar B.host.E)
    (h : ∀ w ∈ Wt, TwProp B.toPre (B.places.resChar w) (k (s w)) (Q (s w)) (χ (s w)))
    (hs : ∀ w ∈ Wt, s (B.places.conj w) = s w) : TwDat B where
  pl := pl
  Q w := if w ∈ Wt then Q (s w) else ∅
  k w := if w ∈ Wt then k (s w) else 0
  psi w := if w ∈ Wt then χ (s w) else 1
  psi_is w := by
    split_ifs with hw
    exacts [(h w hw).1, isPsi_one _]
  psi_ord w := by
    split_ifs with hw
    exacts [(h w hw).2.1, one_pow _]
  psi_tw w := by
    split_ifs with hw
    exacts [(h w hw).2.2.1, Chr.isTwist_one _ _]
  Q_l w := by
    split_ifs with hw
    exacts [(h w hw).2.2.2, fun _ h => absurd h (Finset.notMem_empty _)]
  off w hw := ⟨if_neg fun h => hw (hsub w h), if_neg fun h => hw (hsub w h)⟩
  conj w := by
    by_cases hw : w ∈ Wt
    · have hw' := (hc w).2 hw
      simp only [if_pos hw, if_pos hw', hs w hw, and_self]
    · have hw' := mt (hc w).1 hw
      simp only [if_neg hw, if_neg hw', and_self]

theorem exists_twDat_stagesOn (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (Wt : Set X.B.places.Pl)
    (hsub : ∀ w ∈ Wt, X.B.places.resChar w ∈ pl) (hc : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt)
    (s : X.B.places.Pl → X.toD7.ntw.Tw)
    (hl : ∀ w, X.toD7.ntw.l (s w) = X.B.places.resChar w)
    (hs : ∀ w ∈ Wt, s (X.B.places.conj w) = s w)
    (art : Ideles X.toD7.host.E →* Gab X.toD7.host.E X.toD7.nd.Om) (ha : IsGlobalArtin art)
    (A Q : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (k : X.toD7.ntw.Tw → ℕ)
    (ψ : ∀ i, X.toD7.ntw.RCG i (Q i) →* (X.toD7.ntw.Ok i (k i))ˣ) (ι : ∀ i, RootIso X.toD7 i (k i)) (Av : ℕ → Finset ℕ)
    (hA : ∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i))
    (hψ : ∀ w ∈ Wt, BlochKatoReduction.Gen.PsiOk (s w) (A (s w)) (Q (s w)) (k (s w)) (ψ (s w))) :
    (∀ i, BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) →
      ReadsPick art i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      FrobPick i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      IsPsi (H := X.toD7.host) (X.toD7.ntw.l i) (Q i) (settingChar ha A Q k ψ ι i) ∧
      (settingChar ha A Q k ψ ι i).OrderDvd (X.toD7.ntw.l i ^ k i) ∧
      Chr.IsTwist X.toD7.host (offSet X.B.toPre) (settingChar ha A Q k ψ ι i)) ∧
    ∃ T₁ : TwDat X.B, T₁.pl = pl ∧ T₁.Avoids Av ∧
      (∀ w ∈ Wt, T₁.psi w = settingChar ha A Q k ψ ι (s w) ∧ T₁.Q w = Q (s w) ∧ T₁.k w = k (s w)) ∧
      (∀ w, w ∉ Wt → T₁.psi w = 1 ∧ T₁.Q w = ∅ ∧ T₁.k w = 0) ∧
      ∀ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) → ∃ (B' : Base) (h : Enl X.B B'), (∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z) ∧
        (∀ (w : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar w ^ (pull h T₁).k w = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
        HEq ((pull h T₁).set (tr h.1 Fr f)) (T₁.set f) := by
  classical
  have h1 : ∀ i, BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) →
      ReadsPick art i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      FrobPick i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      IsPsi (H := X.toD7.host) (X.toD7.ntw.l i) (Q i) (settingChar ha A Q k ψ ι i) ∧
      (settingChar ha A Q k ψ ι i).OrderDvd (X.toD7.ntw.l i ^ k i) ∧
      Chr.IsTwist X.toD7.host (offSet X.B.toPre) (settingChar ha A Q k ψ ι i) := fun i hi => by
    rw [settingChar, dif_pos hi]
    exact pickChar_spec ha hi (ι i) fun p hp => hA i p (Or.inl hp)
  have h2 : ∀ w ∈ Wt,
      TwProp X.B.toPre (X.B.places.resChar w) (k (s w)) (Q (s w)) (settingChar ha A Q k ψ ι (s w)) := fun w hw => by
    obtain ⟨-, -, a, b, c⟩ := h1 _ (hψ w hw)
    rw [← hl w]
    exact ⟨a, b, c, fun v hv => (pick_not_over (hψ w hw) hv).1⟩
  refine ⟨h1, ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs, rfl, fun w v hv hm => ?_,
    fun w hw => ⟨if_pos hw, if_pos hw, if_pos hw⟩, fun w hw => ⟨if_neg hw, if_neg hw, if_neg hw⟩, fun S hS => ?_⟩
  · by_cases hw : w ∈ Wt
    · have hv' : v ∈ Q (s w) :=
        (if_pos hw : (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs).Q w = _) ▸ hv
      have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified X.toD7.host.E).1 v).2 ((hψ w hw).1 v hv').2.1
      exact (pick_not_over (hψ w hw) hv').2 (hA (s w) _ (Or.inr (hl w ▸ hm)) hp (Ideal.absNorm_mem _))
    · exact Finset.notMem_empty v
        ((if_neg hw : (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs).Q w = _) ▸ hv)
  · obtain ⟨B', h, a, b⟩ := exists_enl_roots (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs) S hS
    exact ⟨B', h, a, fun w z hz => b (plUnder h w) z (by rwa [resChar_plUnder]), set_pull h _ f⟩

end GlobalTheory.Mem.Top.TwChar

end
