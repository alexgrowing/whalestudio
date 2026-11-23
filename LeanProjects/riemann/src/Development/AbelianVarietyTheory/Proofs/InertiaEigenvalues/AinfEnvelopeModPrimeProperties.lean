import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.dvd_iff_dvd_coeff {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (p : S)
    (hp : ∀ (n : ℕ) (y : S), p * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n) (x : A) :
    s p ∣ x ↔ ∀ i, p ∣ tb.c i x := by
  obtain ⟨h0, -, h2⟩ := GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨_, tb.c_mul i p y⟩
  · choose a ha using h
    obtain ⟨y, hy⟩ := h2 hI a fun n => (tb.fin x (2 * n + 2)).subset fun i hi hi' =>
      hi (hp n _ (ha i ▸ hi'))
    refine ⟨y, sub_eq_zero.1 (h0 _ fun i => ?_)⟩
    rw [map_sub, tb.c_mul, hy, ha, sub_self]

theorem TopBasis.mod_props {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (l : ℕ) (u : S)
    (hp : ∀ (n : ℕ) (y : S), (l : S) * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n)
    (h1 : ∀ y : S, (l : S) * y = 0 → y = 0) (h2 : ∀ y : S, (l : S) ∣ u * y → (l : S) ∣ y)
    (h3 : ∀ y : S, (∀ m : ℕ, ∃ z, (l : S) ∣ y - u ^ m * z) → (l : S) ∣ y) :
    (∀ x : A, (l : A) * x = 0 → x = 0) ∧ (∀ x : A, (l : A) ∣ s u * x → (l : A) ∣ x) ∧
      ∀ x : A, (∀ m : ℕ, ∃ z, (l : A) ∣ x - s u ^ m * z) → (l : A) ∣ x := by
  have key := tb.dvd_iff_dvd_coeff hI (l : S) hp
  rw [← map_natCast s l]
  refine ⟨fun x hx => (GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb).1 x fun i => h1 _ ?_, fun x hx => (key x).2 fun i => h2 _ ?_,
    fun x hx => (key x).2 fun i => h3 _ fun m => ?_⟩
  · rw [← tb.c_mul, hx, map_zero]
  · rw [← tb.c_mul]
    exact (key _).1 hx i
  · obtain ⟨z, hz⟩ := hx m
    refine ⟨tb.c i z, ?_⟩
    rw [← tb.c_mul, ← map_sub, map_pow]
    exact (key _).1 hz i

theorem env_ainf_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En
  obtain ⟨hp, h2, h3, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  exact En.tb.mod_props (ainfObj K).complete.toIsHausdorff l (bk.ev X) hp ainf_torsionFree h2 h3

end GlobalTheory.BSP
