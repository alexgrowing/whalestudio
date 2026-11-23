import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPvSet
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OnePrimeEach

theorem exists_ratPrime_mem {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ w.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem exists_mem_of_prime (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ P.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 L)).injective_int]; exact bot_le)
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := by rw [hQ']; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) (Ideal.mem_bot.1 hmem)

theorem ratPrime_unique {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpw : (p : 𝓞 L) ∈ w.asIdeal) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 L))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hqw)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def ratP (v : HeightOneSpectrum (𝓞 H.F)) : ℕ := (exists_ratPrime_mem v).choose

theorem ratP_prime (v : HeightOneSpectrum (𝓞 H.F)) : (ratP H v).Prime := (exists_ratPrime_mem v).choose_spec.1

theorem ratP_mem (v : HeightOneSpectrum (𝓞 H.F)) : ((ratP H v : ℕ) : 𝓞 H.F) ∈ v.asIdeal :=
  (exists_ratPrime_mem v).choose_spec.2

theorem ratP_eq (v : HeightOneSpectrum (𝓞 H.F)) {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ratP H v = p := ratPrime_unique v (ratP_prime H v) hp (ratP_mem H v) h

def primeK (p : ℕ) : HeightOneSpectrum (𝓞 H.K) :=
  if hp : p.Prime then (exists_mem_of_prime H.K hp).choose else (exists_mem_of_prime H.K Nat.prime_two).choose

theorem primeK_mem {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 H.K) ∈ (primeK H p).asIdeal := by
  unfold primeK
  rw [dif_pos hp]
  exact (exists_mem_of_prime H.K hp).choose_spec

def sel (v : HeightOneSpectrum (𝓞 H.F)) : HeightOneSpectrum (𝓞 H.E) :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose

theorem sel_mem (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ PvSet H (primeK H (ratP H v)) v :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose_spec

theorem sel_above (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ aboveF (L := H.E) H.F v := (sel_mem H v).1

theorem sel_under (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.F) = v := by
  have h := sel_above H v
  rw [aboveF, Set.Finite.mem_toFinset] at h
  exact h

theorem sel_underK (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.K) = primeK H (ratP H v) := (sel_mem H v).2

theorem sel_mem_of {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    sel H v ∈ PvSet H (primeK H p) v := by
  have h := sel_mem H v
  rwa [ratP_eq H v hp hv] at h

def splitPlacesTwoPrimes : PlacesOverCommonPrime H :=
  ⟨primeK H H.pde, primeK H H.pde', primeK_mem H H.pde_prime, primeK_mem H H.pde'_prime, fun v _ => sel H v,
    fun v _ => sel H v, fun v hv => sel_mem_of H H.pde_prime v hv, fun v hv => sel_mem_of H H.pde'_prime v hv⟩

end GlobalTheory.Mem.Top.Bl.OnePrimeEach

open GlobalTheory.Mem.Top.Bl.OnePrimeEach in

theorem GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  intro B
  refine ⟨sel B.host, splitPlacesTwoPrimes B.host, ?_, sel_above B.host, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro v
    exact congrArg HeightOneSpectrum.asIdeal (sel_under B.host v)
  · intro v v' p hp hv hv'
    rw [sel_underK, sel_underK, ratP_eq B.host v hp hv, ratP_eq B.host v' hp hv']

end
