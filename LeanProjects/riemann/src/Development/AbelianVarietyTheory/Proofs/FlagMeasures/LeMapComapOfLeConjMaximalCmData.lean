import Mathlib
import Formalism.LocalRingCardinality.DataSpaces

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramifiedConj

theorem exists_of_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (y : 𝓞 E)
    (hy : RingOfIntegers.mapRingHom (starRingEnd E) y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hfix : star (y : E) = (y : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) hy
    simpa only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply] using h
  obtain ⟨b, hb⟩ := (hc.fixed (y : E)).1 hfix

  have hint : IsIntegral ℤ b := by
    have hy' : IsIntegral ℤ (algebraMap F E b) := by
      rw [hb]
      exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hy'
  refine ⟨⟨b, hint⟩, ?_⟩
  ext
  exact hb

private lemma mem_map_comap_of_star_fixed {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : Ideal (𝓞 E))
    (z : 𝓞 E) (hz : RingOfIntegers.mapRingHom (starRingEnd E) z = z) (hzQ : z ∈ Q) :
    z ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  obtain ⟨a, ha⟩ := exists_of_fixed hc z hz
  rw [← ha]
  apply Ideal.mem_map_of_mem
  rw [Ideal.mem_comap, ha]
  exact hzQ

theorem le_map_comap_of_le_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (P Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (h1 : P ≤ Q) (h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E))) :
    P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  have hinv : ∀ z : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) z) = z := by
    intro z
    ext
    simp only [RingOfIntegers.mapRingHom_apply, starRingEnd_apply, star_star]

  have hD : Ideal.span (Set.range fun θ : 𝓞 E => θ - RingOfIntegers.mapRingHom (starRingEnd E) θ)
      = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨_, _, hU⟩ := hc.cmUnram
    obtain ⟨θ, t, ht, hθ⟩ := hU M hM
    have htθ : t = RingOfIntegers.mapRingHom (starRingEnd E) θ := by
      ext
      rw [RingOfIntegers.mapRingHom_apply, starRingEnd_apply]
      exact ht
    subst htθ
    exact hθ (hDM (Ideal.subset_span ⟨θ, rfl⟩))
  intro x hx
  have hxQ : x ∈ Q := h1 hx
  have hsxQ : RingOfIntegers.mapRingHom (starRingEnd E) x ∈ Q := h2 hx

  have hgen : ∀ θ : 𝓞 E,
      x * (θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) ∈
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro θ
    set s := RingOfIntegers.mapRingHom (starRingEnd E) with hs
    have e : x * (θ - s θ) = (x + s x) * θ - (x * s θ + s x * θ) := by ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
    · refine mem_map_comap_of_star_fixed hc Q _ ?_ (Q.add_mem hxQ hsxQ)
      rw [map_add, hinv]
      ring
    · refine mem_map_comap_of_star_fixed hc Q _ ?_
        (Q.add_mem (Q.mul_mem_right _ hxQ) (Q.mul_mem_right _ hsxQ))
      rw [map_add, map_mul, map_mul, hinv, hinv]
      ring
  have key : ∀ d ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ),
      x * d ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨θ, rfl⟩ := hd
      exact hgen θ
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha
  have h1 : (1 : 𝓞 E) ∈ Ideal.span (Set.range fun θ : 𝓞 E =>
      θ - RingOfIntegers.mapRingHom (starRingEnd E) θ) := by
    rw [hD]
    exact Submodule.mem_top
  simpa using key 1 h1

end GlobalTheory.UnramifiedConj
