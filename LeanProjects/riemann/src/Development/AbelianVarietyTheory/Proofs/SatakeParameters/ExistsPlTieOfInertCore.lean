import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionRingFrobeniusAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldsOkEleven

open NumberField IsDedekindDomain IsLocalRing Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

set_option linter.style.haveILetI false

noncomputable section

namespace GlobalTheory.GO.PlWitt

section Global

variable {E : Type} [Field E] [NumberField E]

def intAlg {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) : A →ₐ[ℤ] B :=
  { f with commutes' := fun r => RingHom.congr_fun (RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)) r }

omit [NumberField E] in

theorem exists_intHom {O Kf : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] (ψ : E →+* Kf) : ∃ g : 𝓞 E →+* O, ∀ x : 𝓞 E, algebraMap O Kf (g x) = ψ x := by
  have h : ∀ x : 𝓞 E, ∃ y : O, algebraMap O Kf y = ψ x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 ((x.isIntegral_coe.map ψ.toIntAlgHom).tower_top)
  choose g hg using h
  have hinj := IsFractionRing.injective O Kf
  exact ⟨{ toFun := g, map_one' := hinj (by simp [hg]), map_mul' := fun a b => hinj (by simp [hg]),
           map_zero' := hinj (by simp [hg]), map_add' := fun a b => hinj (by simp [hg]) }, hg⟩

omit [NumberField E] in

theorem eq_of_cong {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (Q : HeightOneSpectrum (𝓞 E))
    [Algebra.IsUnramifiedAt ℤ Q.asIdeal] (g g' : 𝓞 E →+* O) (hQ : ∀ x, x ∈ Q.asIdeal ↔ g x ∈ maximalIdeal O)
    (h : ∀ x, residue O (g x) = residue O (g' x)) : g = g' := by
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (g y) := fun y => by
    have := y.2
    rw [Ideal.mem_primeCompl_iff, hQ] at this
    simpa using this
  have hu' : ∀ y : Q.asIdeal.primeCompl, IsUnit (g' y) := fun y => by
    have := hu y
    rw [← residue_ne_zero_iff_isUnit] at this ⊢
    rwa [← h]
  let G : Localization.AtPrime Q.asIdeal →+* O := IsLocalization.lift hu
  let G' : Localization.AtPrime Q.asIdeal →+* O := IsLocalization.lift hu'
  have e : (residue O).comp G = (residue O).comp G' :=
    IsLocalization.ringHom_ext Q.asIdeal.primeCompl (RingHom.ext fun x => by simp [G, G', h])
  have := Algebra.FormallyUnramified.ext_of_iInf (R := ℤ) (maximalIdeal O)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top)
    (g₁ := intAlg G) (g₂ := intAlg G') fun x => RingHom.congr_fun e x
  refine RingHom.ext fun x => ?_
  have h2 : G (algebraMap _ _ x) = G' (algebraMap _ _ x) := AlgHom.congr_fun this (algebraMap _ _ x)
  simpa [G, G'] using h2

theorem exists_wittHom (p : ℕ) [Fact p.Prime] (Q : HeightOneSpectrum (𝓞 E)) (hp : (p : 𝓞 E) ∈ Q.asIdeal)
    [Algebra.IsUnramifiedAt ℤ Q.asIdeal] :
    ∃ (n : ℕ) (g : 𝓞 E →+* WittVector p (GaloisField p n)), n ≠ 0 ∧
      Function.Surjective (fun x => WittVector.constantCoeff (g x)) ∧
      ∀ x, x ∈ Q.asIdeal ↔ WittVector.constantCoeff (g x) = 0 := by
  haveI := Q.isMaximal
  letI : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  letI : Fintype (𝓞 E ⧸ Q.asIdeal) := Fintype.ofFinite _
  haveI : CharP (𝓞 E ⧸ Q.asIdeal) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk Q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ Q.asIdeal) p
  letI : Algebra (ZMod p) (𝓞 E ⧸ Q.asIdeal) := ZMod.algebra _ p
  let e := GaloisField.algEquivGaloisFieldOfFintype p n hn
  let W := WittVector p (GaloisField p n)
  let f : 𝓞 E →+* GaloisField p n := e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk Q.asIdeal)
  have hf : ∀ x, x ∈ Q.asIdeal ↔ f x = 0 := fun x => by
    simp [f, Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (f y) := fun y => by
    have := y.2
    rw [Ideal.mem_primeCompl_iff, hf] at this
    exact IsUnit.mk0 _ this
  haveI : Algebra.FinitePresentation ℤ (𝓞 E) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.IsEtaleAt ℤ Q.asIdeal := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  let F : Localization.AtPrime Q.asIdeal →+* W ⧸ Ideal.span {(p : W)} :=
    (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)).symm.toRingHom.comp (IsLocalization.lift hu)
  obtain ⟨G, hG⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (R := ℤ) (intAlg F)
  have key : ∀ x : 𝓞 E, WittVector.constantCoeff (G (algebraMap _ _ x)) = f x := fun x => by
    have h1 : Ideal.Quotient.mk _ (G (algebraMap _ _ x)) = F (algebraMap _ _ x) := AlgHom.congr_fun hG _
    have h2 := congrArg (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)) h1
    have h3 : WittVector.quotientPEquiv (Ideal.Quotient.mk _ (G (algebraMap _ _ x))) = f x := by simpa [F] using h2
    exact h3
  refine ⟨n, G.toRingHom.comp (algebraMap _ _), n.ne_zero, fun y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := (e.surjective.comp Ideal.Quotient.mk_surjective) y
    exact ⟨x, (key x).trans hx⟩
  · exact (hf x).trans (by rw [← key]; rfl)

theorem exists_frob_pow (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {Ω : Type} [Field Ω] (a b : GaloisField p n →+* Ω) :
    (∃ s < n, ∀ x, b x = a (x ^ p ^ s)) := by
  haveI : CharP Ω p := charP_of_injective_ringHom a.injective p
  letI : Algebra (ZMod p) Ω := ZMod.algebra _ p
  let al : (GaloisField p n →+* Ω) → (GaloisField p n →ₐ[ZMod p] Ω) := fun c =>
    { c with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (c.comp (algebraMap _ _)) (algebraMap _ _)) r }
  have hb := FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p n)
  let u : Fin (Module.finrank (ZMod p) (GaloisField p n)) → (GaloisField p n →ₐ[ZMod p] Ω) := fun s =>
    (al a).comp (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p n) ^ s.val)
  have hu : Function.Injective u := fun s t h => hb.1 (AlgHom.ext fun x => a.injective (AlgHom.congr_fun h x))
  have hs : Function.Surjective u := (hu.bijective_of_nat_card_le (by
    simpa using card_algHom_le_finrank (ZMod p) (GaloisField p n) Ω)).2
  obtain ⟨s, hs⟩ := hs (al b)
  refine ⟨s, by simpa [GaloisField.finrank p hn] using s.2, fun x => ?_⟩
  have := AlgHom.congr_fun hs x
  refine this.symm.trans (congrArg a ?_)
  simp [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom]

theorem frob_pow_inj (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : ∀ x : GaloisField p n, x ^ p ^ s = x ^ p ^ t) : s = t := by
  have hb := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p n)).1
  have := @hb ⟨s, by rwa [GaloisField.finrank p hn]⟩ ⟨t, by rwa [GaloisField.finrank p hn]⟩ (AlgHom.ext fun x => by
    simpa [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom] using h x)
  exact congrArg Fin.val this

end Global

section Local

variable {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]

abbrev Wn (n : ℕ) : Type := WittVector p (GaloisField p n)

abbrev Qn (n : ℕ) : Type := FractionRing (Wn p n)

abbrev Fr (n : ℕ) : Qn p n ≃+* Qn p n := WittVector.FractionRing.frobenius p (GaloisField p n)

variable {p} {n : ℕ}

theorem cc_eq_zero (x : Wn p n) : WittVector.constantCoeff x = 0 ↔ (p : Wn p n) ∣ x := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem isUnit_of_cc {x : Wn p n} (h : WittVector.constantCoeff x ≠ 0) : IsUnit x :=
  WittVector.isUnit_of_coeff_zero_ne_zero _ h

theorem fr_pow (s : ℕ) (x : Wn p n) : ∃ y : Wn p n, (Fr p n ^ s) (algebraMap _ _ x) = algebraMap _ _ y ∧
    WittVector.constantCoeff y = WittVector.constantCoeff x ^ p ^ s := by
  induction s with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ s ih =>
    obtain ⟨y, h, hy⟩ := ih
    refine ⟨WittVector.frobenius y, ?_, ?_⟩
    · rw [pow_succ', RingAut.mul_apply, h, SqrtUnif.fractionRing_frobenius_algebraMap]
    · rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, hy,
        ← pow_mul, pow_succ]

def Good (Q : HeightOneSpectrum (𝓞 E)) (i : E →+* Qn p n) : Prop :=
  ∃ g : 𝓞 E →+* Wn p n, (∀ x : 𝓞 E, i x = algebraMap _ _ (g x)) ∧
    Function.Surjective (fun x => WittVector.constantCoeff (g x)) ∧
    ∀ x, x ∈ Q.asIdeal ↔ WittVector.constantCoeff (g x) = 0

theorem exists_good (Q : HeightOneSpectrum (𝓞 E)) (hQ : (p : 𝓞 E) ∈ Q.asIdeal) [Algebra.IsUnramifiedAt ℤ Q.asIdeal] :
    ∃ (n : ℕ) (i : E →+* Qn p n), n ≠ 0 ∧ Good Q i := by
  obtain ⟨n, g, hn, hs, hk⟩ := exists_wittHom p Q hQ
  have hg : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hm := (RingHom.ker_isPrime g).isMaximal h
    have := hm.eq_of_le Q.isPrime.ne_top fun x hx => (hk x).2 (by rw [(RingHom.mem_ker).1 hx, map_zero])
    rw [← this, RingHom.mem_ker, map_natCast] at hQ
    exact (WittVector.irreducible p (k := GaloisField p n)).ne_zero hQ
  have hg' : Function.Injective ((algebraMap (Wn p n) (Qn p n)).comp g) := (IsFractionRing.injective _ _).comp hg
  exact ⟨n, IsFractionRing.lift hg', hn, g, fun x => IsFractionRing.lift_algebraMap hg' x, hs, hk⟩

variable {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n}

omit [NumberField E] in
theorem Good.twist (h : Good Q i) : Good Q ((Fr p n).toRingHom.comp i) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  have e : ∀ x : Wn p n, WittVector.constantCoeff (WittVector.frobenius x) = frobenius _ p (WittVector.constantCoeff x) :=
    fun x => WittVector.coeff_frobenius_charP p x 0
  refine ⟨WittVector.frobenius.comp g, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · exact (congrArg (Fr p n) (hg x)).trans (SqrtUnif.fractionRing_frobenius_algebraMap p _)
  · obtain ⟨x, hx⟩ := ((surjective_frobenius (GaloisField p n) p).comp hs) y
    exact ⟨x, (e _).trans hx⟩
  · rw [hk, RingHom.comp_apply, e, map_eq_zero (frobenius (GaloisField p n) p)]

theorem Good.intAt (h : Good Q i) (x : E) : IntAt Q x ↔ i x ∈ Set.range (algebraMap (Wn p n) (Qn p n)) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have H : ∀ x : E, ∀ r s : 𝓞 E, s ∉ Q.asIdeal → (s : E) * x = r →
      ∃ u : (Wn p n)ˣ, i x = algebraMap _ _ (g r * u) := fun x r s hs h => by
    obtain ⟨u, hu⟩ := isUnit_of_cc (mt (hk s).2 hs)
    refine ⟨u⁻¹, ?_⟩
    have := congrArg i h
    rw [map_mul, hg, hg, ← hu] at this
    rw [map_mul, ← this, mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  constructor
  · rintro ⟨r, s, hs, h⟩
    obtain ⟨u, hu⟩ := H x r s hs h
    exact ⟨_, hu.symm⟩
  · rintro ⟨y, hy⟩
    by_contra hx
    have hv : ∀ z : E, Q.valuation E z ≤ 1 → IntAt Q z := fun z hz => by
      obtain ⟨r, s, h⟩ := Q.exists_primeCompl_mul_eq_of_integer z hz
      exact ⟨r, s, s.2, by rw [mul_comm]; exact h⟩
    have h1 : 1 < Q.valuation E x := lt_of_not_ge fun h => hx (hv x h)
    have hx0 : x ≠ 0 := by rintro rfl; simp at h1
    obtain ⟨r, s, hs, h⟩ := hv x⁻¹ (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h1.le)
    have hr : r ∈ Q.asIdeal := by
      by_contra hr
      exact hx ⟨s, r, hr, by rw [← h]; field_simp⟩
    obtain ⟨u, hu⟩ := H x⁻¹ r s hs h
    have h2 : y * (g r * u) = 1 := hinj (by rw [map_mul, ← hu, hy, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one])
    have h3 := congrArg WittVector.constantCoeff h2
    rw [map_mul, map_mul, (hk r).1 hr] at h3
    simp at h3

omit [NumberField E] in
theorem Good.dense (h : Good Q i) (y : Wn p n) (k : ℕ) :
    ∃ (x : 𝓞 E) (z : Wn p n), i (x : E) = algebraMap (Wn p n) (Qn p n) (y + (p : Wn p n) ^ k * z) := by
  obtain ⟨g, hg, hs, -⟩ := h
  simp only [hg]
  suffices ∃ (x : 𝓞 E) (z : Wn p n), g x = y + (p : Wn p n) ^ k * z by
    obtain ⟨x, z, h⟩ := this
    exact ⟨x, z, congrArg _ h⟩
  induction k with
  | zero => exact ⟨0, -y, by simp⟩
  | succ k ih =>
    obtain ⟨x, z, h⟩ := ih
    obtain ⟨x', hx'⟩ := hs (WittVector.constantCoeff z)
    obtain ⟨z', hz'⟩ := (cc_eq_zero (z - g x')).1 (by rw [map_sub]; exact sub_eq_zero.2 hx'.symm)
    refine ⟨x - p ^ k * x', z', ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, h, pow_succ, mul_assoc, ← hz']
    ring

omit [NumberField E] in
theorem Good.pow_inj (h : Good Q i) (hn : n ≠ 0) {s t : ℕ} (hs : s < n) (ht : t < n)
    (e : ∀ x, (Fr p n ^ s) (i x) = (Fr p n ^ t) (i x)) : s = t := by
  obtain ⟨g, hg, hsur, -⟩ := h
  refine frob_pow_inj p n hn hs ht fun y => ?_
  obtain ⟨x, rfl⟩ := hsur y
  obtain ⟨a, ha, ha'⟩ := fr_pow s (g x)
  obtain ⟨b, hb, hb'⟩ := fr_pow t (g x)
  have := e x
  rw [hg, ha, hb] at this
  simp only
  rw [← ha', ← hb', IsFractionRing.injective (Wn p n) (Qn p n) this]

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]

variable (O) in

def Ov (ψ : E →+* Kf) (Q : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, x ∈ Q.asIdeal ↔ ∃ y ∈ maximalIdeal O, algebraMap O Kf y = ψ x

omit [NumberField E] [IsFractionRing O Kf] in
theorem Ov.eq {ψ : E →+* Kf} {Q Q' : HeightOneSpectrum (𝓞 E)} (h : Ov O ψ Q) (h' : Ov O ψ Q') : Q = Q' :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

omit [IsFractionRing O Kf] in
theorem Ov.conj [StarRing E] {ψ : E →+* Kf} (h : Ov O ψ Q) : Ov O (ψ.comp (starRingEnd E)) (conjPrime₂ Q) :=
  fun x => h (cO E x)

omit [NumberField E] in
theorem ov_iff {ψ : E →+* Kf} {g : 𝓞 E →+* O} (hg : ∀ x : 𝓞 E, algebraMap O Kf (g x) = ψ x) :
    Ov O ψ Q ↔ ∀ x, x ∈ Q.asIdeal ↔ g x ∈ maximalIdeal O := by
  refine forall_congr' fun x => iff_congr Iff.rfl ⟨?_, fun h => ⟨_, h, hg x⟩⟩
  rintro ⟨y, hy, e⟩
  rwa [IsFractionRing.injective O Kf (e.trans (hg x).symm)] at hy

theorem exists_ov (hO : (p : O) ∈ maximalIdeal O) (ψ : E →+* Kf) :
    ∃ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal ∧ Ov O ψ Q := by
  obtain ⟨g, hg⟩ := exists_intHom (O := O) ψ
  have h : (p : 𝓞 E) ∈ (maximalIdeal O).comap g := by rwa [Ideal.mem_comap, map_natCast]
  refine ⟨⟨(maximalIdeal O).comap g, inferInstance, fun e => ?_⟩, h, (ov_iff hg).2 fun x => Iff.rfl⟩
  rw [e, Ideal.mem_bot] at h
  exact hp.out.ne_zero (Nat.cast_eq_zero.1 h)

variable {ι : Qn p n →+* Kf} {j : Wn p n →+* O}

omit [IsFractionRing O Kf] [Algebra O Kf] in
theorem exists_res (hO : (p : O) ∈ maximalIdeal O) (j : Wn p n →+* O) :
    ∃ a : GaloisField p n →+* ResidueField O, ∀ x, a (WittVector.constantCoeff x) = residue O (j x) := by
  refine ⟨RingHom.liftOfSurjective _ (WittVector.constantCoeff_surjective p) ⟨(residue O).comp j, fun x hx => ?_⟩,
    fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  obtain ⟨y, rfl⟩ := (cc_eq_zero x).1 hx
  rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, residue_eq_zero_iff]
  exact Ideal.mul_mem_right _ _ hO

omit [NumberField E] in
theorem Good.ov (h : Good Q i) (hO : (p : O) ∈ maximalIdeal O) (hι : ∀ x, ι (algebraMap _ _ x) = algebraMap O Kf (j x))
    (s : ℕ) {ψ : E →+* Kf} (hψ : ∀ x, ψ x = ι ((Fr p n ^ s) (i x))) : Ov O ψ Q := by
  obtain ⟨g, hg, -, hk⟩ := h
  obtain ⟨a, ha⟩ := exists_res hO j
  intro x
  obtain ⟨y, hy, hy'⟩ := fr_pow s (g x)
  rw [hψ, hg, hy, hι, hk]
  simp only [(IsFractionRing.injective O Kf).eq_iff, exists_eq_right]
  rw [← residue_eq_zero_iff, ← ha, hy', map_eq_zero a, pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)]

theorem Good.exists_pow [Algebra.IsUnramifiedAt ℤ Q.asIdeal] (h : Good Q i) (hn : n ≠ 0) (hO : (p : O) ∈ maximalIdeal O)
    (hι : ∀ x, ι (algebraMap _ _ x) = algebraMap O Kf (j x)) {ψ : E →+* Kf} (hψ : Ov O ψ Q) :
    ∃ s < n, ∀ x, ψ x = ι ((Fr p n ^ s) (i x)) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  obtain ⟨a, ha⟩ := exists_res hO j
  obtain ⟨f, hf⟩ := exists_intHom (O := O) ψ
  have hQ := (ov_iff hf).1 hψ
  let b : GaloisField p n →+* ResidueField O :=
    RingHom.liftOfSurjective (WittVector.constantCoeff.comp g) hs ⟨(residue O).comp f, fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff, ← hQ, hk]; exact hx⟩
  have hb : ∀ x, b (WittVector.constantCoeff (g x)) = residue O (f x) :=
    fun x => RingHom.liftOfRightInverse_comp_apply (WittVector.constantCoeff.comp g) _ _ _ x
  obtain ⟨s, hsn, e⟩ := exists_frob_pow p n hn a b
  let ψ' : E →+* Kf := ι.comp ((Fr p n ^ s).toRingHom.comp i)
  obtain ⟨f', hf'⟩ := exists_intHom (O := O) ψ'
  have : f = f' := eq_of_cong Q f f' hQ fun x => by
    obtain ⟨y, hy, hy'⟩ := fr_pow s (g x)
    have h1 : f' x = j y := IsFractionRing.injective O Kf (by
      rw [hf', ← hι, ← hy, ← hg]; rfl)
    rw [← hb, e, h1, ← ha, hy']
  have h2 : ψ = ψ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x =>
    (hf x).symm.trans (this ▸ hf' x))
  exact ⟨s, hsn, fun x => RingHom.congr_fun h2 x⟩

end Local

section Types

variable {X : Fields} {Kf : Type} [Field Kf] (eK : X.K →+* Kf)

end Types

end GlobalTheory.GO.PlWitt

namespace GlobalTheory.GO

open PlWitt

end GlobalTheory.GO
