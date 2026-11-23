import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsReducedCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OrdModEqLengthQuotSup
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

namespace ReducedCut

open IsLocalRing

theorem length_quot_map_mk {L : Type*} [CommRing L] (J₀ J : Ideal L) :
    Module.length (L ⧸ J₀) ((L ⧸ J₀) ⧸ J.map (Ideal.Quotient.mk J₀)) =
      Module.length L (L ⧸ (J₀ ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := L) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ L J₀ J).toLinearEquiv.length_eq

theorem length_localizedModule_eq_one {B : Type*} [CommRing B] (hB : (⊥ : Ideal B).IsRadical)
    (p : Ideal B) [p.IsPrime] (hp : p ∈ (⊥ : Ideal B).minimalPrimes) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl B) = 1 := by
  have h1 := localMult_eq_one_of_isRadical hB hp
  unfold localMult at h1
  rw [dif_pos ‹p.IsPrime›, Ideal.map_bot] at h1
  have h2 : Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) = 1 := by
    have hne : Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) ≠ ⊤ :=
      fun h => by rw [h] at h1; simp at h1
    rw [← ENat.natCast_toNat hne, h1]
    rfl
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e1 := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl B)
    (Algebra.linearMap B (Localization.AtPrime p))).restrictScalars (Localization.AtPrime p)
  rw [e1.length_eq, ← h2]
  exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq.symm

variable {T : Type} [CommRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime]

local notation "𝓛" => Localization.AtPrime Q
local notation "ι" => algebraMap T (Localization.AtPrime Q)
local notation "𝓘" => Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "𝓐" => Localization.AtPrime Q ⧸ Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "π" => Ideal.Quotient.mk (Ideal.map (algebraMap T (Localization.AtPrime Q)) I)

theorem isRadical_map (hI : I.IsRadical) : (𝓘).IsRadical := by
  show (𝓘).radical ≤ _
  rw [← IsLocalization.map_radical Q.primeCompl (Localization.AtPrime Q) I, hI.radical]

theorem mem_minimalPrimes_map_iff (q : Ideal 𝓛) :
    q ∈ (𝓘).minimalPrimes ↔ q.comap ι ∈ I.minimalPrimes := by
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) I]
  rfl

def under (p : PrimeSpectrum 𝓐) : Ideal T := (p.asIdeal.comap π).comap ι

theorem map_map_under (p : PrimeSpectrum 𝓐) : ((under I Q p).map ι).map π = p.asIdeal := by
  rw [show (under I Q p).map ι = p.asIdeal.comap π from
      IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) _,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem le_comap_mk (p : Ideal 𝓐) : 𝓘 ≤ p.comap π := by
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact p.zero_mem

theorem isRadical_bot (hI : I.IsRadical) : (⊥ : Ideal 𝓐).IsRadical := by
  intro a ha
  obtain ⟨n, hn⟩ := ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact isRadical_map I Q hI ⟨n, hn⟩

theorem length_eq_finsum [IsNoetherianRing T] (hI : I.IsRadical) (hx : ∀ p ∈ I.minimalPrimes, x ∉ p)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) :
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x}))) := by
  classical
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hILrad := isRadical_map I Q hI
  have hsup : (I ⊔ Ideal.span {x}).map (algebraMap T (Localization.AtPrime Q)) =
      I.map (algebraMap T (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap T (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : maximalIdeal (Localization.AtPrime Q) ∈
      (I.map (algebraMap T (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap T (Localization.AtPrime Q) x}).minimalPrimes := by
    rw [← hsup, IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q),
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hQ
  have hILtop : I.map (algebraMap T (Localization.AtPrime Q)) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top
      (top_le_iff.mp (h ▸ (le_sup_left.trans hmax.1.2)))
  have : Nontrivial (Localization.AtPrime Q ⧸ I.map (algebraMap T (Localization.AtPrime Q))) :=
    Ideal.Quotient.nontrivial_iff.mpr hILtop
  have : IsLocalRing (Localization.AtPrime Q ⧸ I.map (algebraMap T (Localization.AtPrime Q))) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmaxc : (maximalIdeal 𝓐).comap π = maximalIdeal 𝓛 :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmaxA : (maximalIdeal 𝓛).map π = maximalIdeal 𝓐 := by
    rw [← hmaxc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

  have hxq : ∀ q ∈ (𝓘).minimalPrimes, ι x ∉ q := fun q hq hxq =>
    hx _ ((mem_minimalPrimes_map_iff I Q q).mp hq) hxq

  have hcomapMin : ∀ p ∈ (⊥ : Ideal 𝓐).minimalPrimes, p.comap π ∈ (𝓘).minimalPrimes := by
    intro p hp
    have h := Ideal.minimalPrimes_comap_of_surjective Ideal.Quotient.mk_surjective hp
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  have hyp : ∀ p ∈ (⊥ : Ideal 𝓐).minimalPrimes, π (ι x) ∉ p :=
    fun p hp h => hxq _ (hcomapMin p hp) (Ideal.mem_comap.mpr h)
  have hyM : π (ι x) ∈ maximalIdeal 𝓐 := by
    rw [← hmaxA]
    exact Ideal.mem_map_of_mem _ (le_sup_right.trans hmax.1.2 (Ideal.mem_span_singleton_self _))

  have hdim : ringKrullDim 𝓐 = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hmaxA]
      exact_mod_cast Ideal.map_height_le_one_of_mem_minimalPrimes hmax
    · obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal 𝓐) ≤ maximalIdeal 𝓐)
      have : p.IsPrime := hp.1.1
      rw [ringKrullDim, Order.one_le_krullDim_iff]
      refine ⟨⟨p, this⟩, ⟨maximalIdeal 𝓐, (maximalIdeal.isMaximal 𝓐).isPrime⟩, ?_⟩
      refine lt_of_le_of_ne (le_maximalIdeal this.ne_top) fun h => hyp p hp ?_
      have h' : p = maximalIdeal 𝓐 := congrArg PrimeSpectrum.asIdeal h
      rw [h']
      exact hyM

  have hinj : ∀ a : 𝓐, π (ι x) * a = 0 → a = 0 := by
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hILrad ?_
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun q hq =>
      ((hq.1.1).mem_or_mem (hq.1.2 ha)).resolve_left (hxq q hq)
  have htors : Module.length 𝓐 (Submodule.torsionBy 𝓐 𝓐 (π (ι x))) = 0 := by
    rw [Module.length_eq_zero_iff]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [hinj a.1 (by simpa using (Submodule.mem_torsionBy_iff _ _).mp a.2),
      hinj b.1 (by simpa using (Submodule.mem_torsionBy_iff _ _).mp b.2)]
  have hann : Module.annihilator 𝓐 𝓐 = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hspan : (Ideal.span {π (ι x)} • ⊤ : Submodule 𝓐 𝓐) = Ideal.span {π (ι x)} := by
    show Ideal.span {π (ι x)} * ⊤ = _
    exact Ideal.mul_top _

  have hL : Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      Module.length 𝓐 (𝓐 ⧸ Ideal.span {π (ι x)}) := by
    rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, hsup, ← length_quot_map_mk,
      Ideal.map_span, Set.image_singleton]
  have hfin := NumbersDVR.length_localizedQuot_ne_top _ Q hQ
  have hC := NumbersDVR.NumbersBirationalInvariance.proof 𝓐 𝓐 (π (ι x)) hdim (by rw [hspan, ← hL]; exact hfin)
  rw [hspan, htors, zero_add, hann] at hC
  rw [hL, hC]

  have hterm : ∀ p : PrimeSpectrum 𝓐, p.asIdeal ∈ (⊥ : Ideal 𝓐).minimalPrimes →
      Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl 𝓐) *
          Module.length 𝓐 (𝓐 ⧸ (p.asIdeal ⊔ Ideal.span {π (ι x)})) =
        Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (under I Q p ⊔ Ideal.span {x}))) := by
    intro p hp
    rw [length_localizedModule_eq_one (isRadical_bot I Q hI) p.asIdeal hp, one_mul,
      ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton,
      show (under I Q p).map ι = p.asIdeal.comap π from
        IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) _]
    have hpeq : p.asIdeal ⊔ Ideal.span {π (ι x)} =
        (p.asIdeal.comap π ⊔ Ideal.span {ι x}).map π := by
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.map_span,
        Set.image_singleton]
    rw [hpeq, length_quot_map_mk, ← sup_assoc, sup_eq_right.mpr (le_comap_mk I Q p.asIdeal)]
  rw [finsum_congr fun p => finsum_congr fun hp => hterm p hp.1]

  have hbij : Set.BijOn (under I Q)
      {p : PrimeSpectrum 𝓐 | p.asIdeal ∈ (⊥ : Ideal 𝓐).minimalPrimes ∧ p.asIdeal ≠ maximalIdeal 𝓐}
      {P | P ∈ I.minimalPrimes ∧ P ≤ Q} := by
    refine ⟨fun p hp => ⟨(mem_minimalPrimes_map_iff I Q _).mp (hcomapMin p.asIdeal hp.1), ?_⟩,
      fun p1 _ p2 _ h => PrimeSpectrum.ext ?_, fun P hP => ?_⟩
    · have h1 : p.asIdeal.comap π ≤ maximalIdeal 𝓛 := by
        rw [← hmaxc]
        exact Ideal.comap_mono (le_maximalIdeal p.isPrime.ne_top)
      exact (Ideal.comap_mono h1).trans Localization.AtPrime.under_maximalIdeal.le
    · rw [← map_map_under I Q p1, ← map_map_under I Q p2, h]
    · obtain ⟨hPmin, hPQ⟩ := hP
      have : P.IsPrime := hPmin.1.1
      have hdisj : Disjoint (Q.primeCompl : Set T) P :=
        Set.disjoint_left.mpr fun a ha haP => ha (hPQ haP)
      have hqc : (P.map ι).comap ι = P :=
        IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) this hdisj
      have hqmin : P.map ι ∈ (𝓘).minimalPrimes := by
        rw [mem_minimalPrimes_map_iff, hqc]
        exact hPmin
      have hpmin : (P.map ι).map π ∈ (⊥ : Ideal 𝓐).minimalPrimes := by
        have h := Ideal.minimalPrimes_map_of_surjective (Ideal.Quotient.mk_surjective (I := 𝓘)) (𝓘)
        rw [Ideal.map_quotient_self, Ideal.mk_ker, sup_idem] at h
        rw [h]
        exact ⟨_, hqmin, rfl⟩
      have : ((P.map ι).map π).IsPrime := hpmin.1.1
      refine ⟨⟨_, this⟩, ⟨hpmin, fun h => hyp _ hpmin (by rw [show (P.map ι).map π = maximalIdeal 𝓐 from h]; exact hyM)⟩, ?_⟩
      show (((P.map ι).map π).comap π).comap ι = P
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hqmin.1.2, hqc]
  refine (finsum_mem_eq_of_bijOn (under I Q) hbij
    (g := fun P => Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (P ⊔ Ideal.span {x}))))
    fun _ _ => rfl).trans ?_

  refine finsum_mem_inter_support_eq' _ _ _ fun P hP => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  by_contra hPQ
  exact Function.mem_support.mp hP (Module.length_eq_zero_iff.mpr
    (NumbersDVR.localizedQuot_subsingleton_of_not_le _ Q fun h => hPQ (le_sup_left.trans h)))

end ReducedCut

theorem ReducedCutLength.intersectionNumber_baseChange : ReducedCutLength.Statement :=
  fun _ _ _ I x Q _ hI hx hQ => ReducedCut.length_eq_finsum I x Q hI hx hQ

end GroundTheory.Heights₂.Heights.Inter
