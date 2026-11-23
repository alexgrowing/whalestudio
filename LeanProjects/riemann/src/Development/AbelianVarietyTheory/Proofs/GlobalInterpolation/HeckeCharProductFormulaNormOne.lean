import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Formalism.L2.Host (HChar atFin upF aboveF IsUnitAt ordF)
open GlobalTheory.CharVal (valuation_conjP conjP_conjP')
open GlobalTheory.NormOneUnit (locK_unr locK_tame exists_of_star_eq under_eq_iff)

namespace GlobalTheory.NormOneProd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]

omit [StarRing E] in

theorem exists_val_eq {P : HeightOneSpectrum (𝓞 E)}
    (hu : ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : Eˣ) :
    ∃ k : Fˣ, P.valuation E ((x / upF F k : Eˣ) : E) = 1 := by
  obtain ⟨k, hk⟩ := (P.under (𝓞 F)).valuation_surjective F (P.valuation E (x : E))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hk
    exact x.ne_zero hk
  refine ⟨Units.mk0 k hk0, ?_⟩
  have hy' : ((x / upF F (Units.mk0 k hk0) : Eˣ) : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  rw [hy', map_div₀, GlobalTheory.MuConj.valuation_up P hu, hk, div_self (by simp)]

theorem split_unit (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P ≠ conjPrime₂ P) {y y' : Eˣ} (hy : (y' : E) = star (y : E))
    (h2 : (conjPrime₂ P).valuation E (y : E) = 1) : χ.locK P y' * χ.locK (conjPrime₂ P) y = 1 := by
  classical
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP
  have he1 : P.valuation E (e : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 he
  have hy0 : P.valuation E (y : E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ he1 (Units.mk0 _ hy0)⁻¹
  have hn' : P.valuation E ((e : E) ^ n * y) < 1 := by
    rw [map_mul, map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
    rwa [← lt_div_iff₀ (zero_lt_iff.2 hy0), one_div]
  have hm : e ^ n - 1 ∈ (conjPrime₂ P).asIdeal := by
    refine Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one e n) ?_
    have : e - 1 = -e' := by rw [← hee]; ring
    rw [this]
    exact neg_mem he'
  obtain ⟨k, hk⟩ := exists_of_star_eq hF hr hc (x := (e : E) ^ n * y + star ((e : E) ^ n * y : E))
    (by rw [star_add, star_star, add_comm])
  have v1 : (conjPrime₂ P).valuation E (algebraMap F E k - y) < 1 := by
    have e1 : algebraMap F E k - y = ((e ^ n - 1 : 𝓞 E) : E) * y + star ((e : E) ^ n * y : E) := by
      rw [hk]; push_cast; ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, h2, mul_one]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    · rw [valuation_conjP, star_star]
      exact hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg, h2] at v1
    exact lt_irrefl _ v1
  have a1 : χ.locK (conjPrime₂ P) (upF F (Units.mk0 k hk0)) = χ.locK (conjPrime₂ P) y := locK_tame (ht _) h2 v1
  have a2 : χ.locK P (upF F (Units.mk0 k hk0)) = χ.locK P y' := by
    refine locK_tame (ht _) (hy ▸ (valuation_conjP P _).symm.trans h2) ?_
    rw [valuation_conjP, star_sub, hF, ← hy] at v1
    exact v1
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  have h := hχ.1 (P.under (𝓞 F)) (Units.mk0 k hk0)
  rwa [HChar.resFin_apply, hab, Finset.prod_pair hP, a1, a2] at h

open Classical in

theorem place_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E),
      ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) (hun : ∀ P, conjPrime₂ P = P → χ.UnrAt P)
    {x z : Eˣ} (hxz : (x : E) = z * star (x : E)) (P : HeightOneSpectrum (𝓞 E)) :
    ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = χ.locK P z := by
  obtain ⟨k, hk⟩ := exists_val_eq (hu (conjPrime₂ P)) x
  set y : Eˣ := x / upF F k with hy
  have hy' : (y : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  have hyz : (y : E) = z * star (y : E) := by
    rw [hy', star_div₀, hF, ← mul_div_assoc, ← hxz]
  have h := hχ.1 (P.under (𝓞 F)) k
  rw [HChar.resFin_apply] at h
  have e1 : ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q y := by
    simp only [hy, map_div, Finset.prod_div_distrib, h, div_one]
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  rw [e1, hab]
  by_cases hP : P = conjPrime₂ P
  · have h1 : P.valuation E (y : E) = 1 := hP ▸ hk
    have h2 : P.valuation E (z : E) = 1 := by
      have h3 := congrArg (P.valuation E) hyz
      rw [map_mul, ← valuation_conjP, hk, h1, mul_one] at h3
      exact h3.symm
    rw [← hP, Finset.pair_eq_singleton, Finset.prod_singleton, locK_unr (hun P hP.symm) h1, locK_unr (hun P hP.symm) h2]
  · have hs0 : star (y : E) ≠ 0 := star_ne_zero.2 y.ne_zero
    have h3 := split_unit hF hr hc hχ ht hP (y' := Units.mk0 _ hs0) rfl hk
    have e2 : y = z * Units.mk0 _ hs0 := Units.ext hyz
    rw [Finset.prod_pair hP, congrArg (χ.locK P) e2, map_mul, mul_assoc, h3, mul_one]

theorem inf_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  intro F E _ _ _ _ _ _ χ rep V x z hF hr hc hu hχ ht hun hrep hxz hV
  classical
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ V.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ V := fun P => by
    simp only [Finset.mem_biUnion, GlobalTheory.Mem.ReadTwist.mem_above, exists_eq_right']
  have h := GlobalTheory.HeckeProduct.productRule χ (V.biUnion (aboveF (L := E) F)) (fun P hP => (hV P fun e => hP ((hm P).2 e)).1) x
  have hfp : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ V.biUnion (aboveF (L := E) F)), χ.val P ^ ordF P x) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    by_cases hP : P ∈ V.biUnion (aboveF (L := E) F)
    · rw [finprod_eq_if, if_neg (not_not.2 hP)]
    rw [finprod_eq_if, if_pos hP, ordF, (hV P fun e => hP ((hm P).2 e)).2, WithZero.log_one, neg_zero, zpow_zero]
  have hpl : ∀ v ∈ V, ∏ Q ∈ aboveF (L := E) F v, χ.locK Q x = χ.locK (rep v) z := fun v _ => by
    have := place_prod hF hr hc hu hχ ht hun hxz (rep v)
    rwa [hrep] at this
  rw [hfp, mul_one, Finset.prod_biUnion, Finset.prod_congr rfl hpl] at h
  · exact h
  · intro v _ w _ hvw
    exact Finset.disjoint_left.2 fun P h1 h2 =>
      hvw ((GlobalTheory.Mem.ReadTwist.mem_above.1 h1).symm.trans (GlobalTheory.Mem.ReadTwist.mem_above.1 h2))

end GlobalTheory.NormOneProd
