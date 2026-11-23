import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace SplitOffPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory

noncomputable def conjSpec {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (cO E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : cO E x ∈ P.asIdeal.comap (cO E) := by
      rw [Ideal.mem_comap, cO_cO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← cO_cO x, h1, map_zero]

theorem exists_mem_not_mem {A : Type} [CommRing A] [IsDedekindDomain A] {Q P P' : HeightOneSpectrum A}
    (h : Q ≠ P) (h' : Q ≠ P') : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal ∧ x ∉ P'.asIdeal := by
  by_contra hc
  have hs : (Q.asIdeal : Set A) ⊆ (P.asIdeal : Set A) ∪ (P'.asIdeal : Set A) := by
    intro x hx
    by_contra hx'
    exact hc ⟨x, hx, fun h1 => hx' (Or.inl h1), fun h1 => hx' (Or.inr h1)⟩
  rcases Ideal.subset_union.1 hs with h1 | h1
  · exact h (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1))
  · exact h' (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P'.isPrime.ne_top h1))

theorem star_sqrt (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  haveI := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem exists_coord (D : D7) (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ u v : ℚ, x = (u : D.host.E) + (v : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.1 hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - D.host.d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v * v' : D.host.E) * sqrt_sq D

theorem exists_norm (D : D7) (x : 𝓞 D.host.K) :
    ∃ (x' : 𝓞 D.host.K) (n : ℤ), algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x' = cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) ∧
      x * x' = (n : 𝓞 D.host.K) := by
  obtain ⟨u, v, huv⟩ := exists_coord D ((x : D.host.K) : D.host.E) (x : D.host.K).2
  have hb : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hst : star ((x : D.host.K) : D.host.E) = (u : D.host.E) - (v : D.host.E) * D.host.sqrtMinusD := by
    rw [huv, star_add, star_mul, star_sqrt, star_ratCast, star_ratCast]; ring
  have hmem : star ((x : D.host.K) : D.host.E) ∈ D.host.K := by
    rw [hst]
    exact sub_mem (SubfieldClass.ratCast_mem _ u) (mul_mem (SubfieldClass.ratCast_mem _ v) hb)
  have hinj : Function.Injective (algebraMap D.host.K D.host.E) := (algebraMap D.host.K D.host.E).injective
  have hint : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) := by
    rw [← isIntegral_algebraMap_iff hinj]
    exact (cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x)).isIntegral_coe
  let x' : 𝓞 D.host.K := ⟨⟨_, hmem⟩, hint⟩
  have hq : ((x * x' : 𝓞 D.host.K) : D.host.K) = algebraMap ℚ D.host.K (u ^ 2 + D.host.d * v ^ 2) := by
    apply hinj
    have e1 : algebraMap D.host.K D.host.E ((x * x' : 𝓞 D.host.K) : D.host.K) =
      ((x : D.host.K) : D.host.E) * star ((x : D.host.K) : D.host.E) := rfl
    rw [e1, hst, ← IsScalarTower.algebraMap_apply, huv, eq_ratCast]
    push_cast
    linear_combination (-(v : D.host.E) ^ 2) * sqrt_sq D
  have hi : IsIntegral ℤ (u ^ 2 + D.host.d * v ^ 2 : ℚ) := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ D.host.K).injective, ← hq]
    exact (x * x').isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨x', n, RingOfIntegers.ext rfl, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

end SplitOffPlaces

open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in

theorem splitOff_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ v ∈ S, ∃ PP ∈ Pg, PP.under (𝓞 D.host.F) = v) → Formalism.IndefR.Bridge.SplitOff P (Pg : Set (HeightOneSpectrum (𝓞 D.host.E))) → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ (∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) ∧ OffS D S P := by
  intro D Pb Pg S P hPg hS hP
  obtain ⟨-, hP1, hP2⟩ := hP
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h e => hP1 (e ▸ h)
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := fun PP h e => hP2 PP h (by rw [e, conjIdeal_eq]; rfl)
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, fun PP h => ⟨hne PP h, fun hc => hne' PP h ?_⟩, ?_⟩
  · intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hg 0 h
    · exact hg 1 h
  · refine HeightOneSpectrum.ext (PP.isMaximal.eq_of_le (conjSpec P).isPrime.ne_top fun c hc' => ?_)
    obtain ⟨c', h1, h2⟩ := hc c hc'
    have e : cO D.host.E c = c' := RingOfIntegers.ext h2.symm
    change cO D.host.E c ∈ P.asIdeal
    rwa [e]
  · intro v hv
    obtain ⟨PP, hPP, rfl⟩ := hS v hv
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (hne PP hPP) (hne' PP hPP)
    have hfix : star ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ha]
      exact (x * cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * cO D.host.E x := RingOfIntegers.ext ha
    refine ⟨⟨a, hint⟩, ?_, fun y hy hyP => ?_⟩
    · change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    · have e' : y = x * cO D.host.E x := RingOfIntegers.ext (hy.trans ha)
      rw [e'] at hyP
      rcases P.isPrime.mem_or_mem hyP with h | h
      · exact hx1 h
      · exact hx2 h

end GlobalTheory
