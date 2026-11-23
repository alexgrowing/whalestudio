import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

namespace PrimeIdem

theorem henselian_of_closure {O B S : Type} [CommRing O] [IsNoetherianRing O] [CommRing B] [Module.Finite ℤ B]
    [CommRing S] (t : O) [IsAdicComplete (Ideal.span {t}) O] (φ : O →+* S) (ψ : B →+* S)
    (h : ∀ T : Subring S, (∀ x, φ x ∈ T) → (∀ x, ψ x ∈ T) → ∀ x, x ∈ T) :
    HenselianRing S (Ideal.span {φ t}) := by
  let _ : Algebra O S := φ.toAlgebra
  let f : O ⊗[ℤ] B →ₐ[O] S :=
    Algebra.TensorProduct.lift (Algebra.ofId O S) ψ.toIntAlgHom fun _ _ => Commute.all _ _
  have hf : Function.Surjective f := fun x => by
    refine h (f : O ⊗[ℤ] B →+* S).range (fun y => ⟨y ⊗ₜ 1, ?_⟩) (fun y => ⟨1 ⊗ₜ y, ?_⟩) x
    · simp [f]; rfl
    · simp [f]
  have : Module.Finite O S := Module.Finite.of_surjective f.toLinearMap hf
  have := GlobalTheory.isAdicComplete_map_of_finite (Ideal.span {t}) S
  rw [Ideal.map_span, Set.image_singleton] at this
  exact IsAdicComplete.henselianRing S (Ideal.span {algebraMap O S t})

theorem exists_idem {S : Type} [CommRing S] (J : Ideal S) [HenselianRing S J] (a : S) (ha : a * a - a ∈ J) :
    ∃ y, y * y = y ∧ y - a ∈ J := by
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial S).Monic := by
    nontriviality S
    monicity!
  obtain ⟨y, hy, hy'⟩ := HenselianRing.is_henselian (I := J) _ hm a (by simpa [sq] using ha) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * a - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    have := J.mul_mem_left 4 ha
    convert this using 1
    simp
    ring)
  refine ⟨y, ?_, hy'⟩
  have : y ^ 2 - y = 0 := by simpa using hy
  linear_combination this

theorem exists_idem_prime {B R : Type} [CommRing B] [IsDedekindDomain B] [CommRing R] (ψ : B →+* R) (g : B)
    (hg : g ≠ 0) (e : R) (he : e * e = e)
    (hH : ∀ a : R, a * a - a ∈ Ideal.span {ψ g} → ∃ x, e * (a + ψ g * x) * (e * (a + ψ g * x)) = e * (a + ψ g * x))
    (hJ : ∀ r : R, ∃ s, e * (1 - ψ g * r) * s = e) (happ : ∀ z : R, ∃ b t, z = ψ b + ψ g * t)
    (w : HeightOneSpectrum B) (hgw : g ∈ w.asIdeal) (hew : 1 - e ∈ w.asIdeal.map ψ) :
    ∃ ε : R, ε * ε = ε ∧ e * ε = ε ∧ 1 - ε ∈ w.asIdeal.map ψ ∧
      (∀ u : HeightOneSpectrum B, u ≠ w → g ∈ u.asIdeal → ε ∈ u.asIdeal.map ψ) ∧
      (∀ z : R, z ∉ w.asIdeal.map ψ → ∃ t, z * t * ε = ε) ∧
      ∀ η ∈ w.asIdeal.map ψ, η * η = η → ε * η = 0 := by
  have h0 : Ideal.span {g} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg
  obtain ⟨k, c, hc, hk⟩ := WfDvdMonoid.max_power_factor h0 w.irreducible
  have hwm := w.isMaximal
  have hcop : IsCoprime w.asIdeal c := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    exact hc (Ideal.dvd_iff_le.2 (le_sup_right.trans (hwm.eq_of_le hne le_sup_left).ge))
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hc
    rw [pow_zero, one_mul] at hk
    rw [← hk]; exact Ideal.dvd_span_singleton.2 hgw
  obtain ⟨a', ha', a, ha, haa⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hmul : ∀ x ∈ (w.asIdeal ^ k).map ψ, ∀ y ∈ c.map ψ, ∃ r, x * y = ψ g * r := fun x hx y hy => by
    have := Ideal.mul_mem_mul hx hy
    rw [← Ideal.map_mul, ← hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
    exact this
  have hgc : g ∈ c := Ideal.dvd_span_singleton.1 (hk ▸ Dvd.intro_left _ rfl)
  have haa' : ψ a' = 1 - ψ a := by rw [← map_one ψ, ← haa, map_add]; ring
  obtain ⟨x, hx⟩ := hH (ψ a) (by
    obtain ⟨r, hr⟩ := hmul _ (Ideal.mem_map_of_mem ψ ha') _ (Ideal.mem_map_of_mem ψ ha)
    rw [Ideal.mem_span_singleton]
    exact ⟨-r, by rw [haa'] at hr; linear_combination -hr⟩)
  set ε := e * (ψ a + ψ g * x) with hε
  have heε : e * ε = ε := by rw [hε, ← mul_assoc, he]
  have hεc : ε ∈ c.map ψ := Ideal.mul_mem_left _ _
    (add_mem (Ideal.mem_map_of_mem ψ ha) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ψ hgc)))
  have hgw' := Ideal.mem_map_of_mem ψ hgw
  refine ⟨ε, hx, heε, ?_, fun u hu hgu => ?_, fun z hz => ?_, fun η hη hηη => ?_⟩
  · have : 1 - ε = (1 - e) + e * ψ a' - e * x * ψ g := by rw [haa', hε]; ring
    rw [this]
    exact sub_mem (add_mem hew (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem ψ (Ideal.pow_le_self hk0 ha'))))
      (Ideal.mul_mem_left _ _ hgw')
  · refine Ideal.map_mono ?_ hεc
    have h1 : u.asIdeal ∣ w.asIdeal ^ k * c := hk ▸ Ideal.dvd_span_singleton.2 hgu
    rcases u.prime.dvd_or_dvd h1 with h | h
    · exact absurd (HeightOneSpectrum.ext (hwm.eq_of_le u.isPrime.ne_top
        (Ideal.le_of_dvd (u.prime.dvd_of_dvd_pow h))).symm) hu
    · exact Ideal.le_of_dvd h
  · obtain ⟨b, t, rfl⟩ := happ z
    have hb : b ∉ w.asIdeal := fun h =>
      hz (add_mem (Ideal.mem_map_of_mem ψ h) (Ideal.mul_mem_right _ _ hgw'))
    have hcb : IsCoprime w.asIdeal (Ideal.span {b}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hb ((le_sup_right.trans (hwm.eq_of_le hne le_sup_left).ge) (Ideal.mem_span_singleton_self b))
    obtain ⟨d, hd, d', hd', hdd⟩ := Ideal.isCoprime_iff_exists.1 (hcb.pow_left (m := k))
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 hd'
    have hdd' : ψ d = 1 - ψ b * ψ q := by rw [← map_one ψ, ← hdd, map_add, map_mul]; ring
    obtain ⟨r, hr⟩ := hmul _ (Ideal.mem_map_of_mem ψ hd) _ hεc
    obtain ⟨s, hs⟩ := hJ (r - t * ψ q * ε)
    rw [hdd'] at hr
    refine ⟨ψ q * s, ?_⟩
    linear_combination ε * hs + (1 - (1 - ψ g * (r - t * ψ q * ε)) * s) * heε - s * ε * hr
      + s * (1 - (ψ b + ψ g * t) * ψ q) * hx
  · have hi : IsIdempotentElem η := hηη
    have h1 : η ∈ (w.asIdeal ^ k).map ψ := by
      rw [Ideal.map_pow, ← hi.pow_eq hk0]; exact Ideal.pow_mem_pow hη k
    obtain ⟨r, hr⟩ := hmul _ h1 _ hεc
    obtain ⟨s, hs⟩ := hJ r
    rw [← hr] at hs
    linear_combination -η * ε * hs - η * heε - e * s * η * η * hx - e * s * ε * hηη

open Formalism.UG Formalism.UG.P

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable abbrev LocInt (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

theorem henselian_locInt (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    HenselianRing (LocInt E v) (Ideal.span {(g : LocInt E v)}) := by
  have hlt : Valued.v ((g : v.adicCompletionIntegers F) : v.adicCompletion F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) g,
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hg
  have := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ hlt
  let φ : v.adicCompletionIntegers F →+* LocInt E v :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)).toRingHom.comp
      (v.adicCompletionIntegers F).subtype).codRestrict _ fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  let ψ : 𝓞 E →+* LocInt E v :=
    ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y =>
      Subring.subset_closure (Or.inl ⟨⟨_, y, rfl⟩, rfl⟩)
  have h := henselian_of_closure (g : v.adicCompletionIntegers F) φ ψ fun T h1 h2 x => by
    have hle : LocInt E v ≤ T.map (LocInt E v).subtype := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
      · exact ⟨_, h2 a, rfl⟩
      · exact ⟨_, h1 y, rfl⟩
    obtain ⟨y, hy, e⟩ := hle x.2
    rwa [← Subtype.ext e]
  rwa [map_natCast] at h

noncomputable def epsV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    IntAf F E := ⟨afsplitEps E v, afsplit_eps_int v⟩

noncomputable def prInt (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    IntAf F E →+* LocInt E v :=
  ((prV (E := E) v).comp (IntAf F E).subtype).codRestrict _ fun y => afsplit_prV_int v y.1 y.2

theorem prInt_surj (v : HeightOneSpectrum (𝓞 F)) : Function.Surjective (prInt E v) := fun y =>
  ⟨⟨afsplitIE v y.1, afsplit_IE_int v y.1 y.2⟩, Subtype.ext (afsplit_prV_IE v y.1)⟩

theorem epsV_mul_eq (v : HeightOneSpectrum (𝓞 F)) {x y : IntAf F E} (h : prInt E v x = prInt E v y) :
    epsV E v * x = epsV E v * y := by
  apply Subtype.ext
  have h' : prV (E := E) v x.1 = prV (E := E) v y.1 := congrArg Subtype.val h
  show afsplitEps E v * x.1 = afsplitEps E v * y.1
  rw [← afsplit_decomp, ← afsplit_decomp, h']

theorem epsV_idem (v : HeightOneSpectrum (𝓞 F)) : epsV E v * epsV E v = epsV E v :=
  Subtype.ext (afsplit_eps_idem v)

theorem epsV_lift (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (a : IntAf F E)
    (ha : a * a - a ∈ Ideal.span {(g : IntAf F E)}) :
    ∃ x, epsV E v * (a + g * x) * (epsV E v * (a + g * x)) = epsV E v * (a + g * x) := by
  have := henselian_locInt (E := E) v g hg
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 ha
  obtain ⟨y, hy, hy'⟩ := exists_idem (Ideal.span {(g : LocInt E v)}) (prInt E v a) (by
    rw [← map_mul, ← map_sub, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 hy'
  obtain ⟨x, rfl⟩ := prInt_surj v d
  have h1 : prInt E v (a + g * x) = y := by
    rw [map_add, map_mul, map_natCast, ← hd]; ring
  have h2 := epsV_mul_eq v (x := (a + (g : IntAf F E) * x) * (a + (g : IntAf F E) * x))
    (y := a + (g : IntAf F E) * x) (by rw [map_mul, h1, hy])
  exact ⟨x, by linear_combination h2 + (a + g * x) * (a + g * x) * epsV_idem (E := E) v⟩

theorem epsV_unit (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (r : IntAf F E) :
    ∃ s, epsV E v * (1 - g * r) * s = epsV E v := by
  have hH := henselian_locInt (E := E) v g hg
  have h1 := Ideal.mem_jacobson_bot.1 (hH.jac (Ideal.mem_span_singleton_self _)) (-prInt E v r)
  obtain ⟨d, hd⟩ := h1.exists_right_inv
  obtain ⟨s, rfl⟩ := prInt_surj v d
  have h2 := epsV_mul_eq v (x := (1 - (g : IntAf F E) * r) * s) (y := 1) (by
    rw [map_mul, map_sub, map_mul, map_natCast, map_one]; linear_combination hd)
  exact ⟨s, by rw [mul_assoc, h2, mul_one]⟩

theorem mem_map_of_apply_eq_zero (u : HeightOneSpectrum (𝓞 E)) (y : Af F) (hy : y ∈ intAd F)
    (h0 : y (u.under (𝓞 F)) = 0) (z : IntAf F E) (hz : z.1 = (1 : E) ⊗ₜ[F] y) :
    z ∈ u.asIdeal.map (Inhab.psi F E) := by
  set v := u.under (𝓞 F) with hv
  obtain ⟨D, hD, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y', hy', e⟩ := integral_adele_approximation_holds F D hD0 y hy
  have hval : ∀ d : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (Af F) d) v) < 1 ↔ d ∈ v.asIdeal := fun d => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rfl
  have hr : r ∈ v.asIdeal := by
    rw [e, afsplit_add_apply, afsplit_mul_apply, add_eq_zero_iff_eq_neg] at h0
    rw [← hval, h0, Valuation.map_neg, map_mul]
    exact (mul_le_of_le_one_right' (hy' v)).trans_lt ((hval D).2 hD)
  have hC : ∀ d : 𝓞 F, (Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) d)).1 =
      (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (Af F) d := fun d => adelstab_incl_C d
  have hz' : z = Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) r) + Inhab.psi F E (algebraMap (𝓞 F) (𝓞 E) D) *
      ⟨(1 : E) ⊗ₜ[F] y', Subring.subset_closure (Or.inr ⟨⟨y', hy'⟩, rfl⟩)⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, hC, hC, hz, e, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      TensorProduct.tmul_add]
  rw [hz']
  exact add_mem (Ideal.mem_map_of_mem _ hr) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hD))

theorem one_sub_epsV_mem (w : HeightOneSpectrum (𝓞 E)) :
    1 - epsV E (w.under (𝓞 F)) ∈ w.asIdeal.map (Inhab.psi F E) := by
  refine mem_map_of_apply_eq_zero w (1 - afsplitI (w.under (𝓞 F)) 1)
    (sub_mem (one_mem _) (afsplitI_mem_intAd _ _ (one_mem _))) ?_ _ ?_
  · rw [afsplit_sub_apply, afsplitI_self, afsplit_one_apply, sub_self]
  · rw [TensorProduct.tmul_sub]; rfl

theorem epsV_mem (v : HeightOneSpectrum (𝓞 F)) (u : HeightOneSpectrum (𝓞 E)) (h : u.under (𝓞 F) ≠ v) :
    epsV E v ∈ u.asIdeal.map (Inhab.psi F E) :=
  mem_map_of_apply_eq_zero u (afsplitI v 1) (afsplitI_mem_intAd _ _ (one_mem _)) (afsplitI_ne v _ h 1) _ rfl

end Adelic

theorem extId_eq_map (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, (Subtype.ext e).symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e ▸ rfl⟩⟩

end PrimeIdem

open PrimeIdem Formalism.UG Formalism.UG.P

theorem exists_prime_idempotent : ∀ (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E)), ∃ ε : IntAf I.F I.E, ε * ε = ε ∧ 1 - ε ∈ extId I w.asIdeal ∧ (∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ extId I u.asIdeal) ∧ (∀ z : IntAf I.F I.E, z ∉ extId I w.asIdeal → ∃ t : IntAf I.F I.E, z * t * ε = ε) ∧ (¬ IsConj I w w → (ε : (I.E ⊗[I.F] Af I.F)) * Formalism.UG.sigR I.cm.sig (Af I.F) ε = 0) := by
  intro I w
  set g : ℕ := Ideal.absNorm w.asIdeal with hgdef
  have hg0 : g ≠ 0 := by rw [hgdef, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hgw : (g : 𝓞 I.E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hun : ∀ u : HeightOneSpectrum (𝓞 I.E), (g : 𝓞 I.F) ∈ (u.under (𝓞 I.F)).asIdeal ↔ (g : 𝓞 I.E) ∈ u.asIdeal :=
    fun u => by
      rw [← map_natCast (algebraMap (𝓞 I.F) (𝓞 I.E)) g]; rfl
  have hgv := (hun w).2 hgw
  obtain ⟨ε, h1, h2, h3, h4, h5, h6⟩ := exists_idem_prime (Inhab.psi I.F I.E) (g : 𝓞 I.E) (by exact_mod_cast hg0)
    (epsV I.E (w.under (𝓞 I.F))) (epsV_idem _)
    (by rw [map_natCast]; exact epsV_lift _ g hgv) (by rw [map_natCast]; exact epsV_unit _ g hgv)
    (by rw [map_natCast]; exact Inhab.exists_approx hg0) w hgw (one_sub_epsV_mem w)
  have h7 : ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ u.asIdeal.map (Inhab.psi I.F I.E) := fun u hu => by
    by_cases h : u.under (𝓞 I.F) = w.under (𝓞 I.F)
    · exact h4 u hu ((hun u).1 (h ▸ hgv))
    · rw [← h2]; exact Ideal.mul_mem_right _ _ (epsV_mem _ u h)
  simp only [extId_eq_map]
  refine ⟨ε, h1, h3, h7, h5, fun hw => ?_⟩
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  let w' : HeightOneSpectrum (𝓞 I.E) := w.comap st fun a => ⟨st a, hst2 a⟩
  have hw' : ∀ a, a ∈ w'.asIdeal ↔ st a ∈ w.asIdeal := fun a => Iff.rfl
  have hne : w' ≠ w := fun e => hw fun a b hab => by
    have : b = st a := RingOfIntegers.ext hab
    rw [this, ← hw', e]
  let σ : IntAf I.F I.E →+* IntAf I.F I.E :=
    ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun y => csDual_sig_mem _ y.2
  have hσ : w'.asIdeal.map (Inhab.psi I.F I.E) ≤ (w.asIdeal.map (Inhab.psi I.F I.E)).comap σ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have e : σ (Inhab.psi I.F I.E a) = Inhab.psi I.F I.E (st a) := Subtype.ext (csDual_sig_incl _ _)
    show σ (Inhab.psi I.F I.E a) ∈ w.asIdeal.map (Inhab.psi I.F I.E)
    rw [e]
    exact Ideal.mem_map_of_mem _ ((hw' a).1 ha)
  exact congrArg Subtype.val (h6 (σ ε) (hσ (h7 w' hne)) (by rw [← map_mul, h1]))

end GlobalTheory.RowLev
