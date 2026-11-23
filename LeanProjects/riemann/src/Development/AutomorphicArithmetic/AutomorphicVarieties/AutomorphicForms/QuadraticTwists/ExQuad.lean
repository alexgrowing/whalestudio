import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.KstarRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.NumberTheory.Padics.Hensel

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_valuationSubring_valuation_prime_lt_one (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hpR : (p : Ω) ∈ R := ⟨p, by simp⟩
  let x : R := ⟨p, hpR⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨⟨r, n, rfl⟩, hr⟩ := h
    have h1 : ((n * p : ℤ) : Ω) = 1 := by
      have := congrArg Subtype.val hr
      simpa [x] using this
    have h2 : n * (p : ℤ) = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨n, by push_cast; linarith⟩
    have h4 : p ∣ 1 := Int.natCast_dvd_natCast.mp h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem ringOfIntegers_rat_exists_int_eq (x : 𝓞 ℚ) : ∃ n : ℤ, x = (n : 𝓞 ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
  have := eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x)
  exact (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm.trans this

private theorem exists_isPlaceOver_natCast_mem_of_valuation_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (p : ℕ)
    (hp0 : p ≠ 0) (h : A.valuation (p : Ω) < 1) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hmem : ∀ x : 𝓞 ℚ, ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) x ∈ A := by
    intro x
    obtain ⟨n, rfl⟩ := ringOfIntegers_rat_exists_int_eq x
    simpa using A.intCast_mem n
  let f : 𝓞 ℚ →+* A := RingHom.codRestrict ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) A hmem
  let I : Ideal (𝓞 ℚ) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x, x ∈ I ↔ A.valuation ((algebraMap ℚ Ω) (x : ℚ)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  have hpI : (p : 𝓞 ℚ) ∈ I := by
    rw [hI]
    simpa using h
  refine ⟨⟨I, Ideal.comap_isPrime f _, ?_⟩, fun x => (hI x).symm, hpI⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hpI
  exact hp0 (by exact_mod_cast hpI)

private theorem false_of_distinct_primes_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hqv : (q : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h1 : (p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have h2 : (((p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q : ℤ) : 𝓞 ℚ) = 1 := by
    rw [h1]
    simp
  have h3 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← h2]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ hpv) (Ideal.mul_mem_right _ _ hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)

private theorem exists_padicInt_sq_eq_neg_of_dvd_one_add (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (p : ℕ) (hdiv : (l : ℤ) ∣ 1 + p) :
    ∃ s : ℤ_[l], s ^ 2 = -(p : ℤ_[l]) := by
  let F : Polynomial ℤ := X ^ 2 + C (p : ℤ)
  have h2 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hd
    have h' : l ∣ 2 := by exact_mod_cast hd
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have ha : (aeval (1 : ℤ_[l])) F = ((1 + p : ℤ) : ℤ_[l]) := by simp [F]
  have hd : (aeval (1 : ℤ_[l])) (derivative F) = ((2 : ℤ) : ℤ_[l]) := by
    simp [F]
    exact map_ofNat _ 2
  have hlt : ‖(aeval (1 : ℤ_[l])) F‖ < ‖(aeval (1 : ℤ_[l])) (derivative F)‖ ^ 2 := by
    rw [ha, hd, h2, one_pow, PadicInt.norm_int_lt_one_iff_dvd]
    exact hdiv
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 + (p : ℤ_[l]) = 0 := by simpa [F] using hz
  linear_combination hz'

private theorem nonempty_ringHom_Kstar_of_sq_eq_neg (l : ℕ) [Fact l.Prime] (p : ℕ) (s : ℚ_[l]) (hs : s ^ 2 = -(p : ℚ_[l])) :
    Nonempty (Kstar p →+* ℚ_[l]) := by
  have hf : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))) = (X - C s) * (X - C (-s)) := by
    have h' : C s ^ 2 = -C (p : ℚ_[l]) := by rw [← C_pow, hs, C_neg]
    rw [map_natCast] at h'
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, map_natCast, Polynomial.map_natCast, C_neg]
    linear_combination h'
  have hsp : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))).Splits := by
    rw [hf]
    exact (Splits.X_sub_C s).mul (Splits.X_sub_C _)
  exact ⟨(SplittingField.lift _ hsp).toRingHom⟩

theorem UpperTheory.V.Af.Cq.exQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : HeightOneSpectrum (𝓞 ℚ) → Prop), (∀ᶠ v in Filter.cofinite, S v) →
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (_ : IsAlgClosure K Ω),
          Module.finrank ℚ K = 2 ∧ Nonempty (K →+* ℚ_[l]) ∧ ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), S v ∧ IsPlaceOver A v ∧
            ∃ s ∈ Ine (F := ℚ) A, s ∉ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range := by
  intro Ω _ instA _ l hl hl2 S hS
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have e : instA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst e
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let P : Set ℕ := {p | p.Prime ∧ 4 * l ∣ p + 1}
  haveI hl0 : NeZero (4 * l) := ⟨by have := hl.out.pos; omega⟩
  have hPinf : P.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun n => ?_
    obtain ⟨p, hpn, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * l) (a := -1) isUnit_one.neg n
    refine ⟨p, ⟨hp, ?_⟩, hpn⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hpm]
    ring
  haveI : Infinite P := hPinf.to_subtype
  have hA : ∀ p : P, ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 :=
    fun p => exists_valuationSubring_valuation_prime_lt_one Ω p p.2.1
  choose Af hAf using hA
  have hv : ∀ p : P, ∃ v : HeightOneSpectrum (𝓞 ℚ),
      IsPlaceOver (Af p) v ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
    fun p => exists_isPlaceOver_natCast_mem_of_valuation_lt_one (Af p) p p.2.1.ne_zero (hAf p)
  choose vf hvf1 hvf2 using hv
  have hinj : Function.Injective vf := by
    intro p q hpq
    by_contra hne
    exact false_of_distinct_primes_mem_asIdeal (vf p) p q p.2.1 q.2.1 (fun h => hne (Subtype.ext h)) (hvf2 p) (hpq ▸ hvf2 q)
  have hfin : (vf ⁻¹' {v | ¬ S v}).Finite :=
    (Filter.eventually_cofinite.mp hS).preimage hinj.injOn
  obtain ⟨p, hpS⟩ := hfin.infinite_compl.nonempty
  have hSv : S (vf p) := by simpa using hpS
  obtain ⟨hp, hdvd⟩ := p.2
  have h4 : 4 ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro l rfl) hdvd
  have hp4 : (p : ℕ) % 4 = 3 := by omega
  have hl' : l ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro_left 4 rfl) hdvd
  have hdiv : (l : ℤ) ∣ 1 + ((p : ℕ) : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hl'
    push_cast at this
    rwa [add_comm] at this
  obtain ⟨s, hs⟩ := exists_padicInt_sq_eq_neg_of_dvd_one_add l hl2 p hdiv
  have hs' : (s : ℚ_[l]) ^ 2 = -((p : ℕ) : ℚ_[l]) := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) hs
    push_cast at this
    exact this
  obtain ⟨ι⟩ := nonempty_ringHom_Kstar_of_sq_eq_neg l p s hs'
  obtain ⟨-, htc, hfr, -⟩ := HV.kstar p hp hp4
  let φ : Kstar p →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI alg : Algebra (Kstar p) Ω := φ.toRingHom.toAlgebra
  haveI tower : IsScalarTower ℚ (Kstar p) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : Algebra.IsAlgebraic (Kstar p) Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) (Kstar p)
  haveI hac : IsAlgClosure (Kstar p) Ω := ⟨inferInstance, inferInstance⟩
  haveI := htc
  haveI : Algebra.IsQuadraticExtension ℚ (Kstar p) := ⟨hfr⟩
  have hram := HV.kstarRam p hp hp4 Ω (Af p) (hAf p)
  obtain ⟨σ, hσI, hσG⟩ := SetLike.not_le_iff_exists.mp hram
  refine ⟨Kstar p, inferInstance, inferInstance, IsCMField.ofCMExtension ℚ (Kstar p), alg, tower, hac,
    hfr, ⟨ι⟩, vf p, Af p, hSv, hvf1 p, σ, hσI, ?_⟩
  rintro ⟨τ, rfl⟩
  apply hσG
  intro x
  exact τ.commutes x
