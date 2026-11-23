import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TameRes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_int_le_one (A : ValuationSubring Ω) (c : 𝓞 E) : A.valuation (algebraMap E Ω (c : E)) ≤ 1 := by
  refine (A.valuation_le_one_iff _).2 ?_
  have hi : IsIntegral ℤ (algebraMap E Ω (c : E)) := c.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom
  have h1 : IsIntegral A (algebraMap E Ω (c : E)) := hi.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem val_le_of_unif {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver (F := E) A P)
    {a b : 𝓞 E} (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) (hb' : b ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω a) ≤ A.valuation (algebraMap E Ω b) := by
  obtain ⟨I, hI⟩ : P.asIdeal ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
  have h1 : ¬ I ≤ P.asIdeal := fun h => hb' (by
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.1 h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (hI ▸ Ideal.mul_mem_mul ha hs)
  have h2 : A.valuation (algebraMap E Ω s) = 1 :=
    le_antisymm (val_int_le_one A s) (not_lt.1 fun h => hs' ((hA s).1 h))
  have h3 := congrArg (fun c : 𝓞 E => A.valuation (algebraMap E Ω c)) ht
  have hint := val_int_le_one (E := E) A t
  simp only [map_mul, RingOfIntegers.coe_eq_algebraMap] at h3 h2 hint ⊢
  rw [h2, mul_one] at h3
  rw [h3]
  exact mul_le_of_le_one_right' hint

theorem redThrough_eq_of_val_sub {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {z w : Ω} (hz : z ∈ A) (hw : w ∈ A)
    (h : A.valuation (z - w) < 1) : redThrough A κ z = redThrough A κ w := by
  unfold redThrough
  rw [dif_pos hz, dif_pos hw]
  congr 1
  apply Ideal.Quotient.eq.2
  exact (A.valuation_lt_one_iff (⟨z, hz⟩ - ⟨w, hw⟩)).2 h

end GlobalTheory.TameRes

namespace GlobalTheory.TameRes

theorem exists_nat_sub_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (hN : normV P = g) (hgP : ((g : ℕ) : 𝓞 E) ∈ P.asIdeal) (u : 𝓞 E) :
    ∃ a : ℕ, a < g ∧ u - (a : 𝓞 E) ∈ P.asIdeal := by
  have hgp : g.Prime := Fact.out
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ P.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (Ideal.Quotient.mk P.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgP
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = g := hN
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hgp.ne_zero)
  let f : ZMod g →+* 𝓞 E ⧸ P.asIdeal := ZMod.castHom (dvd_refl g) _
  have hsurj : Function.Surjective f :=
    (Function.Injective.bijective_of_nat_card_le f.injective (by rw [hcard, Nat.card_zmod])).2
  obtain ⟨x, hx⟩ := hsurj (Ideal.Quotient.mk P.asIdeal u)
  refine ⟨x.val, ZMod.val_lt x, ?_⟩
  apply Ideal.Quotient.eq.1
  rw [← hx, map_natCast]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact map_natCast f x.val

end GlobalTheory.TameRes

open GlobalTheory.TameRes in

theorem GlobalTheory.tameRep_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  intro E Ω _ _ _ _ _ A P g _ hAP hN hgP hgP2 κ σ ζ hσ hζ hT huniq u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hg2 : 2 ≤ g := hgp.two_le
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  have hg4 : 4 ≤ g ^ 2 := by nlinarith

  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hpos : 0 < g ^ 2 - 1 := by omega
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hpos
    have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hy; exact hgΩ hy.symm
    have h2 := hT 2 (by norm_num) y hy
    rw [AlgEquiv.one_apply, div_self hy0, redThrough_one] at h2
    have ho := (hζ 2 (by norm_num)).1
    rw [← h2, orderOf_one] at ho
    omega
  obtain ⟨A', hA'P, hσA', ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hu
  have hAA : A' = A := huniq A' hA'P hσA' hσ1
  rw [hAA] at hv
  rw [hN] at hπ
  simp only [zpow_one] at hv

  have hg1 : 0 < g - 1 := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hg1
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hy; exact hgΩ hy.symm
  have hTy : redThrough A κ (σ y / y) = ζ 1 := hT 1 one_pos y (by rw [pow_one]; exact hy)
  have hϖ0 : algebraMap E Ω (ϖ : E) ≠ 0 := by
    rw [ne_eq, map_eq_zero, RingOfIntegers.coe_eq_zero_iff]
    rintro rfl; exact hϖ2 (zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hπ; exact hϖ0 hπ.symm
  have hϖg : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation ((g : ℕ) : Ω) := by
    have e : ((g : ℕ) : Ω) = algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) := by simp
    rw [e]
    exact le_antisymm (val_le_of_unif hAP hϖ hgP hgP2) (val_le_of_unif hAP hgP hϖ hϖ2)
  have hπy : A.valuation π = A.valuation y := by
    have h1 : A.valuation π ^ (g - 1) = A.valuation y ^ (g - 1) := by
      rw [← map_pow, ← map_pow, hπ, hy, hϖg]
    exact (pow_left_inj hg1.ne').mp h1
  have hvy0 : A.valuation y ≠ 0 := by simpa using hy0
  have hw1 : A.valuation (π / y) = 1 := by rw [map_div₀, hπy, div_self hvy0]
  have hwσ : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw1.le
  have hσy0 : σ y ≠ 0 := fun h => hy0 (σ.injective (by rw [h, map_zero]))
  have key : σ π / π - σ y / y = (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    rw [map_div₀]
    field_simp
  have hq : A.valuation (σ y / y) ≤ 1 := (A.valuation_le_one_iff _).2 (tameQuot_mem A σ hg1 hgΩ hy)
  have h1 : A.valuation (σ π / π - σ y / y) < 1 := by
    rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw1, div_one]
    calc A.valuation (σ y / y) * A.valuation (σ (π / y) - π / y)
        ≤ 1 * A.valuation (σ (π / y) - π / y) := by gcongr
      _ < 1 := by rw [one_mul]; exact hwσ

  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem P g hN hgP u
  have hua' : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 := by
    have := (hAP (u - (a : 𝓞 E))).2 hua
    simpa using this
  have h3 : A.valuation (σ y / y - (a : Ω)) < 1 := by
    have e : σ y / y - (a : Ω) = -(σ π / π - σ y / y) + (σ π / π - algebraMap E Ω (u : E)) +
        (algebraMap E Ω (u : E) - (a : Ω)) := by ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ hv) hua'
    rw [Valuation.map_neg]; exact h1
  have haA : (a : Ω) ∈ A := by exact_mod_cast (natCast_mem A a)
  have hred : redThrough A κ (σ y / y) = (a : Formalism.CyclotomicNorms.Fbar g) := by
    rw [redThrough_eq_of_val_sub κ (tameQuot_mem A σ hg1 hgΩ hy) haA h3]
    unfold redThrough
    rw [dif_pos haA]
    have : (⟨(a : Ω), haA⟩ : A) = (a : A) := Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast]
  have hz : ζ 1 = (a : Formalism.CyclotomicNorms.Fbar g) := by rw [← hTy, hred]
  refine ⟨a, ?_, hua, by rw [map_natCast, hz]⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
  intro hd
  have h0 : (a : Formalism.CyclotomicNorms.Fbar g) = 0 := (CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g a).2 hd
  have ho := (hζ 1 one_pos).1
  rw [hz, h0, pow_one] at ho
  have hz0 : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    exact zero_ne_one
  omega
