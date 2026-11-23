import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas

open Module NumberField IsDedekindDomain Matrix
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ReductionFirst

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]

theorem cO_coe (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

theorem cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩

theorem hcompl_le_Tw (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩

theorem smul_coe {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v :=
  (algebraMap_smul K r v).symm

def InS (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop :=
  ∃ s ∈ Tw w, ∃ r : 𝓞 K, (s : K) * x = r

theorem InS.star' {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : InS w x) : InS w (star x) := by
  obtain ⟨s, hs, r, hr⟩ := h
  refine ⟨cO K s, cO_mem_Tw hs, cO K r, ?_⟩
  rw [cO_coe, cO_coe, ← hr, star_mul']

theorem common_den {w : HeightOneSpectrum (𝓞 K)} {ι : Type*} (S : Finset ι) (x : ι → K)
    (h : ∀ k ∈ S, InS w (x k)) : ∃ s ∈ Tw w, ∀ k ∈ S, ∃ r : 𝓞 K, (s : K) * x k = r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, (Tw w).one_mem, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨t, ht, hS⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    obtain ⟨s, hs, r, hr⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨s * t, (Tw w).mul_mem hs ht, ?_⟩
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact ⟨t * r, by show (s : K) * (t : K) * x k = (t : K) * (r : K); linear_combination (t : K) * hr⟩
    · obtain ⟨r', hr'⟩ := hS k hk
      exact ⟨s * r', by show (s : K) * (t : K) * x k = (s : K) * (r' : K); linear_combination (s : K) * hr'⟩

theorem vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  simp [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (m : ℕ) :
    vw w (a ^ m) = (m : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_unit (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (hr : r ∉ w.asIdeal) :
    vw w (r : K) = 0 := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {r} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr0
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ]
  have h2 : ¬ w.asIdeal ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hr
  have h3 := mt (Associates.count_ne_zero_iff_dvd hJ w.irreducible).1 h2
  rw [not_not] at h3
  simp [h3]

theorem Tw_ne_zero {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem

theorem hform_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) :
    hform H y x = star y ⬝ᵥ (H *ᵥ x) := by
  rw [hform, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem main {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) (l g : ℕ) (hl : 0 < l)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M)
    (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K) (he : IsLocBasis (matLat P M) w e) :
    vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K) :=
  _root_.UpperTheory.Reformulated.B.SelectionLemmas.main H P M hM l g hl hdual w e he

end ReductionFirst

theorem reduction_lemma_first : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he

end Formalism.DivisionValues
