import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E)
include hc

theorem rll_cO_algebraMap (a : 𝓞 F) : cO E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (cO E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [algebraMap_cO]
  have e : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap F E (algebraMap (𝓞 F) F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact (hc.fixed _).2 ⟨_, rfl⟩

theorem IsOver.conj {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (h : IsOver v P) : IsOver v (conjPrime₂ P) := by
  unfold IsOver at h ⊢
  rw [h]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_conjP, rll_cO_algebraMap hc]

theorem rll_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem rll_over_cases {v : HeightOneSpectrum (𝓞 F)} {P Q : Pl E} (hP : IsOver v P) (hQ : IsOver v Q) :
    Q = P ∨ Q = conjPrime₂ P := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := Formalism.L2.DIV.crtPl ({Q, P, conjPrime₂ P} : Finset (Pl E)) (fun R => if R = Q then 0 else 1)
  have h1 : a ∈ Q.asIdeal := by
    have := ha Q (by simp)
    simpa using this
  have hnot : ∀ R : Pl E, R ≠ Q → R ∈ ({Q, P, conjPrime₂ P} : Finset (Pl E)) → a ∉ R.asIdeal := by
    intro R hR hm haR
    have := ha R hm
    rw [if_neg hR] at this
    exact (Ideal.ne_top_iff_one _).1 R.isPrime.ne_top (by
      have h2 := Ideal.sub_mem _ haR this
      simpa using h2)
  have h2 := hnot P (Ne.symm hne.1) (by simp)
  have h3 := hnot (conjPrime₂ P) (Ne.symm hne.2) (by simp)
  obtain ⟨b, hb⟩ := rll_norm_mem hc a
  have hbv : b ∈ v.asIdeal := by
    rw [hQ, Ideal.mem_comap, hb]; exact Ideal.mul_mem_right _ _ h1
  rw [hP, Ideal.mem_comap, hb] at hbv
  rcases P.isPrime.mem_or_mem hbv with h | h
  · exact h2 h
  · exact h3 ((mem_conjP P a).2 h)

theorem BasePi.over_unique {ST : Finset (Pl E)} {π : 𝓞 E} (h : BasePi ST π) {v : HeightOneSpectrum (𝓞 F)} {P : Pl E}
    (hP : P ∈ ST) (hov : IsOver v P) : ∀ Q ∈ ST, IsOver v Q → Q = P := by
  intro Q hQ hQv
  rcases rll_over_cases hc hov hQv with e | e
  · exact e
  · exfalso
    have h1 : π ∈ (conjPrime₂ P).asIdeal := e ▸ h.mem hQ
    exact h.conj_notMem hP ((mem_conjP P π).1 h1)

theorem mem_plUnder_iff_norm {S : Finset (Pl E)} {ϖ : 𝓞 E} (hS : ∀ P : Pl E, P ∈ S ↔ ϖ ∈ P.asIdeal) (N : ℕ)
    (hN : ϖ * cO E ϖ = (N : 𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) : v ∈ plUnder F S ↔ (N : 𝓞 F) ∈ v.asIdeal := by
  constructor
  · rintro ⟨P, hP, hv⟩
    rw [hv, Ideal.mem_comap, map_natCast, ← hN]
    exact Ideal.mul_mem_right _ _ ((hS P).1 hP)
  · intro hv
    obtain ⟨P, hP⟩ := Formalism.L2.DIV.exists_overPl (E := E) v
    have hP' : IsOver v P := hP
    have h1 : (N : 𝓞 E) ∈ P.asIdeal := by
      rw [hP, Ideal.mem_comap, map_natCast] at hv; exact hv
    rw [← hN] at h1
    rcases P.isPrime.mem_or_mem h1 with h | h
    · exact ⟨P, (hS P).2 h, hP'⟩
    · exact ⟨conjPrime₂ P, (hS _).2 ((mem_conjP P ϖ).2 h), hP'.conj hc⟩

end Places

section Host

variable {X : Fields} {Pr : Primes X}

theorem basePi_of_ok (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) : BasePi (Pr.vT u) (Pr.piT u) where
  dvd r := by
    have h0 : Pr.piT u ≠ 0 := by
      intro h0
      obtain ⟨a, b, hab⟩ := hPr.piT_cop u
      rw [h0, map_zero, mul_zero, mul_zero, add_zero] at hab
      exact zero_ne_one hab
    constructor
    · intro hr
      exact piT_dvd_of_mem hX hPr u r fun P => hr P.1 P.2
    · rintro ⟨q, rfl⟩ P hP
      exact Ideal.mul_mem_right _ _ ((mem_divs h0 P).1 hP)
  cop := hPr.piT_cop u

open Classical in

theorem plUnder_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal := by
  have key : ∀ i, v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := fun i => by
    have hne : X.conjO (Pr.piG i) ≠ 0 := by
      intro h0
      have := hPr.piG_norm i
      rw [h0, mul_zero] at this
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) this.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs hne P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
    rw [h2, mul_comm]; exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, ho⟩
    rcases Finset.mem_union.1 hP with h | h
    · exact Or.inl ⟨P, h, ho⟩
    · exact Or.inr ⟨P, h, ho⟩
  · rintro (⟨P, hP, ho⟩ | ⟨P, hP, ho⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, ho⟩
    · exact ⟨P, Finset.mem_union_right _ hP, ho⟩

end Host

end Formalism.L2.Col
