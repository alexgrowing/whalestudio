import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped nonZeroDivisors

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def atP (p : HeightOneSpectrum (𝓞 F)) (I : FractionalIdeal (𝓞 E)⁰ E) (t : E) : Prop :=
  ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ algebraMap F E (a : F) * t ∈ I

theorem int_smul_mem (I : FractionalIdeal (𝓞 E)⁰ E) (b : 𝓞 F) (t : E) (ht : t ∈ I) :
    algebraMap F E (b : F) * t ∈ I := by
  have hb : IsIntegral ℤ (algebraMap F E (b : F)) := by
    first
    | exact IsIntegral.map (algebraMap F E).toIntAlgHom b.isIntegral_coe
    | exact (b.isIntegral_coe).algebraMap
    | exact IsIntegral.map (IsScalarTower.toAlgHom ℤ F E) b.isIntegral_coe
  let z : 𝓞 E := ⟨algebraMap F E (b : F), hb⟩
  have hz : algebraMap F E (b : F) * t = z • t := by
    rw [Algebra.smul_def]
    rfl
  rw [hz]
  first
  | exact (I : Submodule (𝓞 E) E).smul_mem z ht
  | exact Submodule.smul_mem _ z ht

theorem mem_iff_forall_atP (I : FractionalIdeal (𝓞 E)⁰ E) (t : E) :
    t ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 F), atP p I t := by
  constructor
  · intro h p
    refine ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
    rw [show ((1 : 𝓞 F) : F) = 1 from rfl, map_one, one_mul]
    exact h
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {a | algebraMap F E (a : F) * t ∈ I}
        add_mem' := fun {a b} ha hb => by
          have ha' : algebraMap F E (a : F) * t ∈ I := ha
          have hb' : algebraMap F E (b : F) * t ∈ I := hb
          change algebraMap F E ((a : F) + (b : F)) * t ∈ I
          rw [map_add, add_mul]
          exact Submodule.add_mem (I : Submodule (𝓞 E) E) ha' hb'
        zero_mem' := by
          change algebraMap F E (0 : F) * t ∈ I
          rw [map_zero, zero_mul]
          exact Submodule.zero_mem (I : Submodule (𝓞 E) E)
        smul_mem' := fun c a ha => by
          have ha' : algebraMap F E (a : F) * t ∈ I := ha
          change algebraMap F E ((c : F) * (a : F)) * t ∈ I
          rw [map_mul, mul_assoc]
          exact int_smul_mem I c _ ha' }
    by_contra hne
    have hJ : J ≠ ⊤ := by
      intro hJ
      have h1 : (1 : 𝓞 F) ∈ J := by rw [hJ]; exact Submodule.mem_top
      have h1' : algebraMap F E ((1 : 𝓞 F) : F) * t ∈ I := h1
      rw [show ((1 : 𝓞 F) : F) = 1 from rfl, map_one, one_mul] at h1'
      exact hne h1'
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
    have hM0 : M ≠ ⊥ := by
      first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      | (intro h0; subst h0; exact NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 hM))
    obtain ⟨a, ha, hat⟩ := h ⟨M, hM.isPrime, hM0⟩
    exact ha (hJM hat)

theorem exists_den (p : HeightOneSpectrum (𝓞 F)) (y : F) (hy : p.valuation F y ≤ 1) :
    ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ ∃ z : 𝓞 F, (a : F) * y = (z : F) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : (algebraMap (𝓞 F) F d) ≠ 0 := by
    simpa using hd0
  have hsp : Ideal.span {d} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0
  obtain ⟨k, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hsp p.irreducible
  have h1 : p.intValuation d ≤ WithZero.exp (-(k : ℤ)) :=
    (p.intValuation_le_pow_iff_dvd d k).2 ⟨J, hfac⟩
  have h2 : p.intValuation n ≤ p.intValuation d := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at hy
    have hpos : 0 < p.intValuation d := by
      rw [zero_lt_iff]; exact p.intValuation_ne_zero d hd0
    exact (div_le_one₀ hpos).1 hy
  have h3 : p.asIdeal ^ k ∣ Ideal.span {n} := (p.intValuation_le_pow_iff_dvd n k).1 (h2.trans h1)
  have hn : n ∈ p.asIdeal ^ k := (Ideal.dvd_iff_le.1 h3) (Ideal.mem_span_singleton_self n)
  have hJp : ¬ J ≤ p.asIdeal := fun h => hJ (Ideal.dvd_iff_le.2 h)
  obtain ⟨a, haJ, hap⟩ := Set.not_subset.1 hJp
  have hna : n * a ∈ Ideal.span {d} := by rw [hfac]; exact Ideal.mul_mem_mul hn haJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hna
  refine ⟨a, hap, z, ?_⟩
  have hz' : (z : F) * (d : F) = (n : F) * (a : F) := by
    rw [← map_mul, ← map_mul, hz]
  field_simp
  linear_combination -hz'

end Gen

section LocS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem cmul (a b : 𝓞 F) : ((a * b : 𝓞 F) : F) = (a : F) * (b : F) := by
  first
  | rfl
  | push_cast; ring
  | simp

private theorem vle_iff_valuation_le (x y : A.Fp) : (x ≤ᵥ y) ↔ valuation A.Fp x ≤ valuation A.Fp y := by
  first
  | exact Valuation.Compatible.vle_iff_le x y
  | exact Valuation.Compatible.vle_iff_le
  | exact ValuativeRel.vle_iff_le x y
  | exact ValuativeRel.vle_iff_le
  | exact (ValuativeRel.vle_iff_le x y).symm
  | simp [Valuation.Compatible.vle_iff_le]

private theorem mem_valuationSubring_iff_valuation_le_one (x : A.Fp) : x ∈ 𝒪[A.Fp] ↔ valuation A.Fp x ≤ 1 := by
  first
  | exact Valuation.mem_integer_iff _ _
  | exact Iff.rfl
  | (rw [← map_one (valuation A.Fp)]; exact vle_iff_valuation_le A x 1)
  | simp [Valuation.mem_integer_iff]
  | (rw [← map_one (valuation A.Fp), ← vle_iff_valuation_le A x 1]; exact Iff.rfl)

theorem val_iff (a b : F) : valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF b) ↔ p.valuation F a ≤ p.valuation F b := by
  exact (vle_iff_valuation_le A _ _).symm.trans (A.val a b)

theorem mem_OF_iff (a : F) : A.ιF a ∈ 𝒪[A.Fp] ↔ p.valuation F a ≤ 1 := by
  have h := val_iff A a 1
  simp only [map_one] at h
  rw [mem_valuationSubring_iff_valuation_le_one A]
  exact h

theorem val_eq_one (a : 𝓞 F) (ha : a ∉ p.asIdeal) : p.valuation F (a : F) = 1 := by
  change p.valuation F (algebraMap (𝓞 F) F a) = 1
  first
  | (rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]; exact ha)
  | (rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 ha)
  | exact le_antisymm (p.valuation_le_one a) (not_lt.1 fun h => ha ((p.valuation_lt_one_iff_mem a).1 h))

theorem vFp_eq_one (a : F) (ha : p.valuation F a = 1) : valuation A.Fp (A.ιF a) = 1 := by
  have h1 := val_iff A a 1
  have h2 := val_iff A 1 a
  simp only [map_one] at h1 h2
  exact le_antisymm (h1.2 ha.le) (h2.2 ha.ge)

instance nontrivEp : Nontrivial A.Ep :=
  Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

theorem alg_mem_O (b : A.Fp) (hb : b ∈ 𝒪[A.Fp]) : algebraMap A.Fp A.Ep b ∈ A.O := by
  rw [A.O_def]
  have h : IsIntegral 𝒪[A.Fp] (algebraMap 𝒪[A.Fp] A.Ep ⟨b, hb⟩) := isIntegral_algebraMap
  first
  | exact h
  | (rw [IsScalarTower.algebraMap_apply 𝒪[A.Fp] A.Fp A.Ep] at h; exact h)
  | simpa using h

private theorem mem_valuationSubring_of_isIntegral' (b : A.Fp) (h : IsIntegral 𝒪[A.Fp] b) : b ∈ 𝒪[A.Fp] := by
  first
  | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (valuation A.Fp)).mem_of_integral h
     rw [← hy]; exact y.2)
  | (obtain ⟨y, hy⟩ := (Valuation.integer.integers _).mem_of_integral h
     rw [← hy]; exact y.2)
  | (obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
     rw [← hy]; exact y.2)

theorem mem_OF_of_alg (b : A.Fp) (h : algebraMap A.Fp A.Ep b ∈ A.O) : b ∈ 𝒪[A.Fp] := by
  rw [A.O_def] at h
  apply mem_valuationSubring_of_isIntegral' A
  first
  | exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep) (algebraMap A.Fp A.Ep).injective).1 h
  | exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep) (FaithfulSMul.algebraMap_injective A.Fp A.Ep)).1 h

theorem ιE_int (z : 𝓞 E) : A.ιE (z : E) ∈ A.O := by
  rw [A.O_def]
  have hz : IsIntegral ℤ (A.ιE (z : E)) := IsIntegral.map A.ιE.toIntAlgHom z.isIntegral_coe
  first
  | exact hz.tower_top
  | exact IsIntegral.tower_top (A := 𝒪[A.Fp]) hz

theorem cj_mem (x : A.Ep) (h : x ∈ A.O) : A.cj x ∈ A.O := by
  rw [A.O_def] at h ⊢
  first
  | exact h.map ((A.cj : A.Ep →ₐ[A.Fp] A.Ep).restrictScalars 𝒪[A.Fp])
  | exact IsIntegral.map (A.cj.toAlgHom.restrictScalars 𝒪[A.Fp]) h

theorem scal_iff (S : Set A.Ep) (hS : ∀ b ∈ 𝒪[A.Fp], ∀ z ∈ S, algebraMap A.Fp A.Ep b * z ∈ S) (b b' : A.Fp) (hb : b ≠ 0)
    (hb' : b' ≠ 0) (hv : valuation A.Fp b = valuation A.Fp b') (z : A.Ep) :
    algebraMap A.Fp A.Ep b * z ∈ S ↔ algebraMap A.Fp A.Ep b' * z ∈ S := by
  have key : ∀ c c' : A.Fp, c ≠ 0 → valuation A.Fp c = valuation A.Fp c' →
      algebraMap A.Fp A.Ep c * z ∈ S → algebraMap A.Fp A.Ep c' * z ∈ S := by
    intro c c' hc hv h
    have hu : c' / c ∈ 𝒪[A.Fp] := by
      (rw [mem_valuationSubring_iff_valuation_le_one A, map_div₀, ← hv, div_self ((Valuation.ne_zero_iff _).2 hc)]) <;> exact le_rfl
    have h2 := hS _ hu _ h
    have e : c' / c * c = c' := by field_simp
    rwa [← mul_assoc, ← map_mul, e] at h2
  exact ⟨key b b' hb hv, key b' b hb' hv.symm⟩

theorem O_scal : ∀ b ∈ 𝒪[A.Fp], ∀ z ∈ (A.O : Set A.Ep), algebraMap A.Fp A.Ep b * z ∈ (A.O : Set A.Ep) :=
  fun b hb z hz => A.O.mul_mem (alg_mem_O A b hb) hz

theorem ιE_alg (a : F) : A.ιE (algebraMap F E a) = algebraMap A.Fp A.Ep (A.ιF a) := A.compat a

private theorem exists_integer_eq_algebraMap_integer (b : 𝓞 F) : ∃ z : 𝓞 E, (z : E) = algebraMap F E (b : F) := by
  have hb : IsIntegral ℤ (algebraMap F E (b : F)) := by
    first
    | exact IsIntegral.map (algebraMap F E).toIntAlgHom b.isIntegral_coe
    | exact (b.isIntegral_coe).algebraMap
  exact ⟨⟨algebraMap F E (b : F), hb⟩, rfl⟩

theorem int_iff (hinv : ∀ x, sig (sig x) = x) (hfix : ∀ x : E, sig x = x → ∃ a : F, algebraMap F E a = x) (x : E) :
    A.ιE x ∈ A.O ↔ atP p 1 x := by
  obtain ⟨tr, htr⟩ := hfix (x + sig x) (by rw [map_add, hinv, add_comm])
  obtain ⟨nm, hnm⟩ := hfix (x * sig x) (by rw [map_mul, hinv, mul_comm])
  have hq : x * x - algebraMap F E tr * x + algebraMap F E nm = 0 := by
    rw [htr, hnm]
    ring
  constructor
  · intro hx
    have hsx : A.ιE (sig x) ∈ A.O := by
      rw [← A.cj_ιE]
      exact cj_mem A _ hx
    have htrO : A.ιF tr ∈ 𝒪[A.Fp] := by
      apply mem_OF_of_alg A
      rw [← A.compat, htr, map_add]
      exact A.O.add_mem hx hsx
    have hnmO : A.ιF nm ∈ 𝒪[A.Fp] := by
      apply mem_OF_of_alg A
      rw [← A.compat, hnm, map_mul]
      exact A.O.mul_mem hx hsx
    obtain ⟨a1, ha1, z1, hz1⟩ := exists_den p tr ((mem_OF_iff A tr).1 htrO)
    obtain ⟨a2, ha2, z2, hz2⟩ := exists_den p nm ((mem_OF_iff A nm).1 hnmO)
    refine ⟨a1 * a2, fun h => (p.isPrime.mem_or_mem h).elim ha1 ha2, ?_⟩
    obtain ⟨U, hU⟩ := exists_integer_eq_algebraMap_integer (E := E) (a2 * z1)
    obtain ⟨V, hV⟩ := exists_integer_eq_algebraMap_integer (E := E) (a1 * a1 * a2 * z2)
    have hyint : IsIntegral (𝓞 E) (algebraMap F E ((a1 * a2 : 𝓞 F) : F) * x) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C U * Polynomial.X + Polynomial.C V, ?_, ?_⟩
      · first
        | monicity!
        | monicity
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
        have eU : algebraMap (𝓞 E) E U = algebraMap F E ((a2 : F) * (z1 : F)) := hU
        have eV : algebraMap (𝓞 E) E V = algebraMap F E ((a1 : F) * (a1 : F) * (a2 : F) * (z2 : F)) := hV
        have e1 : ((a1 * a2 : 𝓞 F) : F) = (a1 : F) * (a2 : F) := rfl
        rw [eU, eV, e1, ← hz1, ← hz2]
        simp only [map_mul]
        linear_combination (algebraMap F E (a1 : F) * algebraMap F E (a2 : F)) ^ 2 * hq
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyint
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨w, hw⟩
  · rintro ⟨a, ha, hax⟩
    rw [FractionalIdeal.mem_one_iff] at hax
    obtain ⟨z, hz⟩ := hax
    have hzO : A.ιE (algebraMap F E (a : F) * x) ∈ A.O := by
      rw [← hz]
      exact ιE_int A z
    rw [map_mul, A.compat] at hzO
    have hv : valuation A.Fp (A.ιF (a : F)) = 1 := vFp_eq_one A _ (val_eq_one a ha)
    have hinvO : (A.ιF (a : F))⁻¹ ∈ 𝒪[A.Fp] := by
      (rw [mem_valuationSubring_iff_valuation_le_one A, map_inv₀, hv, inv_one]) <;> exact le_rfl
    have hne : A.ιF (a : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have h2 := O_scal A _ hinvO _ hzO
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul] at h2
    exact h2

end LocS

section LocS2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem ιE_div' (t : E) (a : F) :
    A.ιE (t / algebraMap F E a) = algebraMap A.Fp A.Ep ((A.ιF a)⁻¹) * A.ιE t := by
  have h : t / algebraMap F E a = algebraMap F E a⁻¹ * t := by rw [map_inv₀, div_eq_inv_mul]
  rw [h, map_mul, A.compat, map_inv₀]

theorem cond_gen (c : F) (ν gp ot : ℕ) (hg : ((gp : ℕ) : A.Fp) ≠ 0) (ho : ((ot : ℕ) : A.Fp) ≠ 0)
    (hvo : valuation A.Fp ((ot : ℕ) : A.Fp) = 1) (k : ℕ) (y : E) :
    A.ιE (y / algebraMap F E ((((gp * ot : ℕ)) : F) ^ k * c ^ ν)) ∈ A.O ↔
      algebraMap A.Fp A.Ep ((((gp : ℕ) : A.Fp) ^ k)⁻¹) * (algebraMap A.Fp A.Ep (((A.ιF c) ^ ν)⁻¹) * A.ιE y) ∈ A.O := by
  rw [ιE_div' A]
  have hι : A.ιF ((((gp * ot : ℕ)) : F) ^ k * c ^ ν) = (((gp : ℕ) : A.Fp) * ((ot : ℕ) : A.Fp)) ^ k * (A.ιF c) ^ ν := by
    simp [map_mul, map_pow, map_natCast]
  rw [hι, ← mul_assoc, ← map_mul]
  by_cases hC : (A.ιF c) ^ ν = 0
  · simp [hC]
  · refine scal_iff A (A.O : Set A.Ep) (O_scal A) _ _ ?_ ?_ ?_ _
    · exact inv_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hg ho)) hC)
    · exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hg)) (inv_ne_zero hC)
    · simp only [map_inv₀, map_mul, map_pow, hvo, one_pow, mul_one, mul_inv]

theorem tw_gen (b : A.Fp) (s : ℕ) (t : E) :
    algebraMap A.Fp A.Ep b * A.ιE (t - (-1) ^ s * sig t) =
      algebraMap A.Fp A.Ep b * A.ιE t - (-1) ^ s * A.cj (algebraMap A.Fp A.Ep b * A.ιE t) := by
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, AlgEquiv.commutes, A.cj_ιE]
  ring

end LocS2

section LocGenS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {p : HeightOneSpectrum (𝓞 F)}

theorem one_notMem (p : HeightOneSpectrum (𝓞 F)) : (1 : 𝓞 F) ∉ p.asIdeal :=
  fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem memLocalization_of_mem {I : FractionalIdeal (𝓞 E)⁰ E} {t : E} (h : t ∈ I) : atP p I t := by
  refine ⟨1, one_notMem p, ?_⟩
  rw [show ((1 : 𝓞 F) : F) = 1 from rfl, map_one, one_mul]
  exact h

theorem mul_notMem {a b : 𝓞 F} (ha : a ∉ p.asIdeal) (hb : b ∉ p.asIdeal) : a * b ∉ p.asIdeal :=
  fun h => (p.isPrime.mem_or_mem h).elim ha hb

theorem memLocalization_add {I : FractionalIdeal (𝓞 E)⁰ E} {x y : E} (hx : atP p I x) (hy : atP p I y) : atP p I (x + y) := by
  obtain ⟨a, ha, h⟩ := hx
  obtain ⟨b, hb, h'⟩ := hy
  refine ⟨a * b, mul_notMem ha hb, ?_⟩
  have e : algebraMap F E ((a * b : 𝓞 F) : F) * (x + y) =
      algebraMap F E (b : F) * (algebraMap F E (a : F) * x) + algebraMap F E (a : F) * (algebraMap F E (b : F) * y) := by
    rw [cmul, map_mul]; ring
  rw [e]
  exact (I : Submodule (𝓞 E) E).add_mem (int_smul_mem I b _ h) (int_smul_mem I a _ h')

theorem memLocalization_mul {I J : FractionalIdeal (𝓞 E)⁰ E} {x y : E} (hx : atP p I x) (hy : atP p J y) : atP p (I * J) (x * y) := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, mul_notMem ha hb, ?_⟩
  have e : algebraMap F E ((a * b : 𝓞 F) : F) * (x * y) =
      (algebraMap F E (a : F) * x) * (algebraMap F E (b : F) * y) := by
    rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul]
    ring
  rw [e]
  exact FractionalIdeal.mul_mem_mul hax hby

theorem memLocalization_of_smul {I : FractionalIdeal (𝓞 E)⁰ E} {a : 𝓞 F} (ha : a ∉ p.asIdeal) {x : E}
    (h : atP p I (algebraMap F E (a : F) * x)) : atP p I x := by
  obtain ⟨b, hb, h⟩ := h
  refine ⟨b * a, mul_notMem hb ha, ?_⟩
  rw [show ((b * a : 𝓞 F) : F) = (b : F) * (a : F) from rfl, map_mul, mul_assoc]
  exact h

def LocGen (p : HeightOneSpectrum (𝓞 F)) (I : FractionalIdeal (𝓞 E)⁰ E) (c : E) : Prop :=
  c ≠ 0 ∧ ∀ x : E, atP p I x ↔ atP p 1 (x / c)

theorem LocGen.one : LocGen p (1 : FractionalIdeal (𝓞 E)⁰ E) 1 :=
  ⟨one_ne_zero, fun x => by rw [div_one]⟩

theorem LocGen.self {I : FractionalIdeal (𝓞 E)⁰ E} {c : E} (h : LocGen p I c) : atP p I c := by
  refine (h.2 c).2 ?_
  rw [div_self h.1]
  apply memLocalization_of_mem
  first
  | exact FractionalIdeal.one_mem_one _
  | exact FractionalIdeal.one_mem_one
  | simp

theorem LocGen.mul {I J : FractionalIdeal (𝓞 E)⁰ E} {c c' : E} (h : LocGen p I c) (h' : LocGen p J c') :
    LocGen p (I * J) (c * c') := by
  have hs := h.self
  have hs' := h'.self
  obtain ⟨hc, hI⟩ := h
  obtain ⟨hc', hJ⟩ := h'
  refine ⟨mul_ne_zero hc hc', fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := hx
    apply memLocalization_of_smul ha
    have key : ∀ w ∈ I * J, atP p 1 (w / (c * c')) := by
      intro w hw
      exact FractionalIdeal.mul_induction_on (C := fun w => atP p 1 (w / (c * c'))) hw
        (fun i hi j hj => by
          have h3 := memLocalization_mul ((hI i).1 (memLocalization_of_mem hi)) ((hJ j).1 (memLocalization_of_mem hj))
          rw [one_mul] at h3
          show atP p 1 (i * j / (c * c'))
          rw [← div_mul_div_comm]
          exact h3)
        (fun y z hy hz => by
          have hy' : atP p 1 (y / (c * c')) := hy
          have hz' : atP p 1 (z / (c * c')) := hz
          show atP p 1 ((y + z) / (c * c'))
          rw [add_div]
          exact memLocalization_add hy' hz')
    have h4 := key _ hax
    rwa [mul_div_assoc] at h4
  · have h3 := memLocalization_mul (memLocalization_mul hs hs') hx
    rw [mul_one] at h3
    have e : c * c' * (x / (c * c')) = x := by
      field_simp
    rwa [e] at h3

theorem LocGen.pow {I : FractionalIdeal (𝓞 E)⁰ E} {c : E} (h : LocGen p I c) (n : ℕ) : LocGen p (I ^ n) (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact LocGen.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem LocGen.span {c : E} (hc : c ≠ 0) : LocGen p (FractionalIdeal.spanSingleton (𝓞 E)⁰ c) c := by
  refine ⟨hc, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    rw [FractionalIdeal.mem_spanSingleton] at hax
    obtain ⟨z, hz⟩ := hax
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def] at hz
    rw [← mul_div_assoc, ← hz]
    field_simp
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    rw [FractionalIdeal.mem_one_iff] at hax
    obtain ⟨z, hz⟩ := hax
    rw [FractionalIdeal.mem_spanSingleton]
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, hz]
    field_simp

end LocGenS

section Typed

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

variable {ell : ℕ} (sg : SplitAt A.Fp A.Ep A.cj ell)

theorem e_alg (c : A.Fp) : sg.e (algebraMap A.Fp A.Ep c) = (c, c) := by
  rw [AlgEquiv.commutes]
  first
  | rfl
  | simp [Prod.algebraMap_apply]

theorem O_split (x : A.Ep) : x ∈ A.O ↔ (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by
  rw [A.O_def]
  have hres : ∀ y : A.Fp, y ∈ 𝒪[A.Fp] → IsIntegral 𝒪[A.Fp] y := fun y hy => by
    have h : IsIntegral 𝒪[A.Fp] (algebraMap 𝒪[A.Fp] A.Fp ⟨y, hy⟩) := isIntegral_algebraMap
    exact h
  constructor
  · intro h
    have h2 : IsIntegral 𝒪[A.Fp] (sg.e x) := h.map (sg.e.toAlgHom.restrictScalars 𝒪[A.Fp])
    exact ⟨mem_valuationSubring_of_isIntegral' A _ (h2.map ((AlgHom.fst A.Fp A.Fp A.Fp).restrictScalars 𝒪[A.Fp])),
      mem_valuationSubring_of_isIntegral' A _ (h2.map ((AlgHom.snd A.Fp A.Fp A.Fp).restrictScalars 𝒪[A.Fp]))⟩
  · rintro ⟨h1, h2⟩
    have h3 : IsIntegral 𝒪[A.Fp] (sg.e x) := IsIntegral.pair (hres _ h1) (hres _ h2)
    have h4 := h3.map (sg.e.symm.toAlgHom.restrictScalars 𝒪[A.Fp])
    first
    | simpa using h4
    | (rw [show (sg.e.symm.toAlgHom.restrictScalars 𝒪[A.Fp]) (sg.e x) = x from sg.e.symm_apply_apply x] at h4; exact h4)

theorem typed_iff (s : ℕ) (X : A.Ep) :
    sg.e (sg.e.symm ((sg.e X).1, (-1) ^ s * (sg.e X).2) * algebraMap A.Fp A.Ep ((sg.q : A.Fp)⁻¹)) ∈
        Formalism.FourierDecayAlt.I.orderR (𝒪[A.Fp]) (sg.q : A.Fp) ↔
      algebraMap A.Fp A.Ep ((sg.q : A.Fp)⁻¹) * X ∈ A.O ∧
        algebraMap A.Fp A.Ep (((sg.q : A.Fp) ^ 2)⁻¹) * (X - (-1) ^ s * A.cj X) ∈ A.O := by
  have hq0 : (sg.q : A.Fp) ≠ 0 := fun h0 => sg.q_irr.ne_zero (by
    first
    | exact Subtype.ext h0
    | exact_mod_cast h0
    | simpa using h0)
  have hS : ((-1 : A.Fp) ^ s) * (-1) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hsO : ((-1 : A.Fp) ^ s) ∈ 𝒪[A.Fp] := pow_mem (neg_mem (one_mem _)) s
  have hq1 : (sg.q : A.Fp) * ((sg.q : A.Fp) ^ 2)⁻¹ = (sg.q : A.Fp)⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
  have hD : ∀ a b : A.Fp, a * (sg.q : A.Fp)⁻¹ - (-1) ^ s * b * (sg.q : A.Fp)⁻¹ =
      (sg.q : A.Fp) * (((sg.q : A.Fp) ^ 2)⁻¹ * (a - (-1) ^ s * b)) := by
    intro a b
    linear_combination (-(a - (-1) ^ s * b)) * hq1
  have hD2 : ∀ a b : A.Fp, ((sg.q : A.Fp) ^ 2)⁻¹ * (b - (-1) ^ s * a) =
      -((-1) ^ s) * (((sg.q : A.Fp) ^ 2)⁻¹ * (a - (-1) ^ s * b)) := by
    intro a b
    linear_combination (-((sg.q : A.Fp) ^ 2)⁻¹ * b) * hS
  have e1 : sg.e (sg.e.symm ((sg.e X).1, (-1) ^ s * (sg.e X).2) * algebraMap A.Fp A.Ep ((sg.q : A.Fp)⁻¹)) =
      ((sg.e X).1 * (sg.q : A.Fp)⁻¹, (-1) ^ s * (sg.e X).2 * (sg.q : A.Fp)⁻¹) := by
    simp only [map_mul, AlgEquiv.apply_symm_apply, e_alg A sg]
    first
    | rfl
    | simp
  have e2 : sg.e (algebraMap A.Fp A.Ep ((sg.q : A.Fp)⁻¹) * X) =
      ((sg.q : A.Fp)⁻¹ * (sg.e X).1, (sg.q : A.Fp)⁻¹ * (sg.e X).2) := by
    simp only [map_mul, e_alg A sg]
    first
    | rfl
    | simp
  have e3 : sg.e (algebraMap A.Fp A.Ep (((sg.q : A.Fp) ^ 2)⁻¹) * (X - (-1) ^ s * A.cj X)) =
      (((sg.q : A.Fp) ^ 2)⁻¹ * ((sg.e X).1 - (-1) ^ s * (sg.e X).2),
        ((sg.q : A.Fp) ^ 2)⁻¹ * ((sg.e X).2 - (-1) ^ s * (sg.e X).1)) := by
    simp only [map_mul, map_sub, map_pow, map_neg, map_one, e_alg A sg, sg.e_cj]
    ext <;> simp
  rw [O_split A sg, O_split A sg, e1, e2, e3]
  simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, t, ht, hteq⟩
    have htD : t = ((sg.q : A.Fp) ^ 2)⁻¹ * ((sg.e X).1 - (-1) ^ s * (sg.e X).2) :=
      mul_left_cancel₀ hq0 (hteq.symm.trans (hD _ _))
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [mul_comm]
      exact h1
    · have h3 := mul_mem hsO h2
      rw [show (-1 : A.Fp) ^ s * ((-1) ^ s * (sg.e X).2 * (sg.q : A.Fp)⁻¹) =
        (-1) ^ s * (-1) ^ s * ((sg.q : A.Fp)⁻¹ * (sg.e X).2) by ring, hS, one_mul] at h3
      exact h3
    · rw [← htD]
      exact ht
    · rw [hD2, ← htD]
      exact mul_mem (neg_mem hsO) ht
  · rintro ⟨⟨r1, r2⟩, r3, r4⟩
    refine ⟨?_, ?_, _, r3, hD _ _⟩
    · rw [mul_comm]
      exact r1
    · rw [show (-1 : A.Fp) ^ s * (sg.e X).2 * (sg.q : A.Fp)⁻¹ = (-1) ^ s * ((sg.q : A.Fp)⁻¹ * (sg.e X).2) by ring]
      exact mul_mem hsO r2

end Typed

section Rec

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices

variable {D : Formalism.BasicNotions.D7}

theorem conjF_inv (x : D.host.E) : D.conjF (D.conjF x) = x := by
  simp only [D.conjF_eq]
  have hc : ∀ y, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    (D.host.der.conj_iff D.host.φ₀ D.host.conj).2 (by
      first
      | simp only [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]
      | rfl
      | simp [Formalism.HC.HostRaw.conj])
  apply D.host.φ₀.injective
  rw [hc, hc, Complex.conj_conj]

theorem conjF_fix (x : D.host.E) (h : D.conjF x = x) : ∃ a : D.host.F, algebraMap D.host.F D.host.E a = x := by
  have hx : x ∈ D.host.F := (D.host.der.mem_F x).2 (by rw [← D.conjF_eq]; exact h)
  refine ⟨⟨x, hx⟩, ?_⟩
  first
  | rfl
  | simp

theorem natCast_mem_iff (p : PlF D) (n : ℕ) : ((n : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ↔ Loc.resChar p ∣ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  first
  | exact ringChar.spec _ n
  | (simp only [Loc.resChar]; exact ringChar.spec _ n)

def oth (p : PlF D) : ℕ :=
  if Loc.resChar p = D.host.g 0 then D.host.g 1
  else if Loc.resChar p = D.host.g 1 then D.host.g 0 else D.host.g 0 * D.host.g 1

theorem gpart_mul_oth (p : PlF D) : gpart p * oth p = Lat.gS D := by
  simp only [gpart, oth, Lat.gS]
  split_ifs <;> ring

theorem gpart_ne_zero (p : PlF D) : gpart p ≠ 0 := by
  have hl := ((D.s.atP p).ellPrime).out
  simp only [gpart]
  split_ifs with h0 h1
  · rw [← h0]
    exact hl.ne_zero
  · rw [← h1]
    exact hl.ne_zero
  · exact one_ne_zero

theorem oth_not_dvd (p : PlF D) : ¬ Loc.resChar p ∣ oth p := by
  have hl := ((D.s.atP p).ellPrime).out
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have gne := D.host.g_ne
  simp only [oth]
  split_ifs with h0 h1
  · rw [h0]
    intro hd
    exact gne ((Nat.prime_dvd_prime_iff_eq hg0 hg1).1 hd)
  · rw [h1]
    intro hd
    exact gne ((Nat.prime_dvd_prime_iff_eq hg1 hg0).1 hd).symm
  · intro hd
    rcases (Nat.Prime.dvd_mul hl).1 hd with hd | hd
    · exact h0 ((Nat.prime_dvd_prime_iff_eq hl hg0).1 hd)
    · exact h1 ((Nat.prime_dvd_prime_iff_eq hl hg1).1 hd)

theorem oth_ne_zero (p : PlF D) : oth p ≠ 0 := by
  intro h
  apply oth_not_dvd p
  rw [h]
  exact dvd_zero _

theorem unitAt_eq (p : PlF D) : uP p = ((oth p : ℕ) : ℚ)⁻¹ := by
  have hg : ((gpart p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (gpart_ne_zero p)
  have ho : ((oth p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (oth_ne_zero p)
  simp only [uP]
  rw [← gpart_mul_oth p, Nat.cast_mul]
  first
  | (rw [div_mul_eq_div_div, div_self hg, one_div])
  | field_simp

theorem v_nat (p : PlF D) (n : ℕ) (h : ¬ Loc.resChar p ∣ n) :
    valuation (D.s.atP p).Fp ((n : ℕ) : (D.s.atP p).Fp) = 1 := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := fun hm => h ((natCast_mem_iff p n).1 hm)
  have h2 := val_eq_one (p := p) ((n : ℕ) : 𝓞 D.host.F) h1
  have h2' : p.valuation D.host.F ((n : ℕ) : D.host.F) = 1 := by
    first
    | simpa using h2
    | exact_mod_cast h2
  have h3 := vFp_eq_one (D.s.atP p) ((n : ℕ) : D.host.F) h2'
  simpa using h3

theorem gpart_none (p : PlF D) (h : (D.s.atP p).split = none) : gpart p = 1 := by
  have h1 : ¬ Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
    rw [← D.s_split p, h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1
  unfold gpart
  rw [if_neg h1.1, if_neg h1.2]

theorem gpart_some (p : PlF D) (sg) (h : (D.s.atP p).split = some sg) : gpart p = Loc.resChar p := by
  have h1 : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
    rw [← D.s_split p, h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  unfold gpart
  split_ifs with h0 h2
  · exact h0.symm
  · exact h2.symm
  · exact absurd h1 (by tauto)

theorem qE_eq (p : PlF D) : qE p = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((gpart p : ℕ) : (D.s.atP p).Fp) := by
  rcases h : (D.s.atP p).split with _ | sg
  · simp only [qE, h]
    rw [gpart_none p h]
    simp
  · simp only [qE, h]
    rw [gpart_some p sg h, sg.q_eq]

theorem twist_none (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) (h : (D.s.atP p).split = none) : twist p s x = x := by
  simp only [twist, h]

theorem twist_some (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) (sg) (h : (D.s.atP p).split = some sg) :
    twist p s x = sg.e.symm ((sg.e x).1, (-1) ^ s * (sg.e x).2) := by
  simp only [twist, h]

theorem twist_alg (p : PlF D) (s : ℕ) (b : (D.s.atP p).Fp) (x : (D.s.atP p).Ep) :
    twist p s (algebraMap _ _ b * x) = algebraMap _ _ b * twist p s x := by
  rcases h : (D.s.atP p).split with _ | sg
  · simp only [twist, h]
  · simp only [twist, h]
    apply sg.e.injective
    simp only [AlgEquiv.apply_symm_apply, map_mul, e_alg (D.s.atP p) sg]
    ext <;> simp <;> ring

theorem inverse_alg {K R : Type} [Field K] [CommRing R] [Algebra K R] (b : K) (hb : b ≠ 0) :
    Ring.inverse (algebraMap K R b) = algebraMap K R b⁻¹ := by
  have hu : IsUnit (algebraMap K R b) := (IsUnit.mk0 b hb).map (algebraMap K R)
  have h1 : algebraMap K R b * algebraMap K R b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  calc Ring.inverse (algebraMap K R b)
      = Ring.inverse (algebraMap K R b) * (algebraMap K R b * algebraMap K R b⁻¹) := by rw [h1, mul_one]
    _ = algebraMap K R b⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem natFp_ne_zero (p : PlF D) (n : ℕ) (hn : n ≠ 0) : ((n : ℕ) : (D.s.atP p).Fp) ≠ 0 := by
  haveI := (D.s.atP p).char0
  exact Nat.cast_ne_zero.2 hn

theorem tMod_eq (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (hδ : δ p ≠ 0) (ν s : ℕ) (t : D.host.E) :
    tMod δ p ν s t =
      algebraMap _ _ (((δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) ^ ν)⁻¹) *
        (twist p s ((D.s.atP p).ιE t) * algebraMap _ _ (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹)) := by
  have hoth : ((oth p : ℕ) : (D.s.atP p).Fp) ≠ 0 := natFp_ne_zero p _ (oth_ne_zero p)
  have hg : ((gpart p : ℕ) : (D.s.atP p).Fp) ≠ 0 := natFp_ne_zero p _ (gpart_ne_zero p)
  have hu : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((oth p : ℕ) : (D.s.atP p).Fp)⁻¹) := by
    rw [unitAt_eq p]
    have e : (((((oth p : ℕ) : ℚ))⁻¹ : ℚ) : D.host.E) =
        algebraMap D.host.F D.host.E (((oth p : ℕ) : D.host.F)⁻¹) := by
      simp [map_inv₀, map_natCast]
    rw [e, (D.s.atP p).compat, map_inv₀, map_natCast]
  simp only [tMod]
  rw [hu, qE_eq p, ← map_mul, ← map_pow, inverse_alg _ (pow_ne_zero _ (mul_ne_zero hδ (inv_ne_zero hoth))),
    inverse_alg _ hg, mul_assoc]

end Rec

section Rec2

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices

variable {D : Formalism.BasicNotions.D7}

theorem R_scal {K R : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [CommRing R] [Algebra K R] [TopologicalSpace R]
    [MeasurableSpace R] (Mp : Loc.Model K R) :
    ∀ b ∈ 𝒪[K], ∀ z ∈ (Mp.R : Set R), algebraMap K R b * z ∈ (Mp.R : Set R) := by
  intro b hb z hz
  have halg : algebraMap K R b ∈ Mp.R := by
    rcases h : Mp.split with _ | g
    · simp only [Loc.Model.R, h]
      rw [Mp.L.O_def]
      have hi : IsIntegral 𝒪[K] (algebraMap 𝒪[K] R ⟨b, hb⟩) := isIntegral_algebraMap
      exact hi
    · simp only [Loc.Model.R, h]
      refine Subring.mem_comap.2 (Subring.mem_map.2 ⟨(⟨b, hb⟩, ⟨b, hb⟩), ?_, ?_⟩)
      · first
        | rfl
        | exact (RingHom.mem_eqLocus _).2 rfl
        | simp
      · first
        | (ext <;> simp [AlgEquiv.commutes])
        | simp [AlgEquiv.commutes]
  exact Mp.R.mul_mem halg hz

theorem twist_membership_iff_integral (p : PlF D) (Mp : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hO : Mp.L.O = (D.s.atP p).O)
    (hm : (Mp.split = none ∧ (D.s.atP p).split = none) ∨
      ∃ g sg, Mp.split = some g ∧ (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q) (s : ℕ) (X : (D.s.atP p).Ep) :
    twist p s X * algebraMap _ _ (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹) ∈ Mp.R ↔
      algebraMap _ _ (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹) * X ∈ (D.s.atP p).O ∧
      algebraMap _ _ ((((gpart p : ℕ) : (D.s.atP p).Fp) ^ 2)⁻¹) * (X - (-1) ^ s * (D.s.atP p).cj X) ∈ (D.s.atP p).O := by
  rcases hm with ⟨h1, h2⟩ | ⟨g, sg, h1, h2, he, hq⟩
  · rw [twist_none p s X h2, gpart_none p h2]
    simp only [Nat.cast_one, inv_one, one_pow, map_one, mul_one, one_mul]
    have hR : Mp.R = (D.s.atP p).O := by
      simp only [Loc.Model.R, h1]
      exact hO
    rw [hR]
    constructor
    · intro hX
      exact ⟨hX, sub_mem hX (mul_mem (pow_mem (neg_mem (one_mem _)) s) (cj_mem (D.s.atP p) X hX))⟩
    · exact fun h => h.1
  · rw [twist_some p s X sg h2, gpart_some p sg h2, ← sg.q_eq, ← typed_iff (D.s.atP p) sg s X]
    have key : ∀ Y : (D.s.atP p).Ep, Y ∈ Mp.R ↔
        sg.e Y ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[(D.s.atP p).Fp]) ((sg.q : (D.s.atP p).Fp)) := by
      intro Y
      simp only [Loc.Model.R, h1, Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
      rw [he, ← hq, Subring.mem_comap, Subring.mem_map]
      constructor
      · rintro ⟨w, hw, hwY⟩
        have hw' : Ideal.Quotient.mk (Ideal.span {g.q}) w.1 = Ideal.Quotient.mk (Ideal.span {g.q}) w.2 := hw
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hw'
        obtain ⟨c, hc⟩ := hw'
        have e1 : (sg.e Y).1 = (w.1 : (D.s.atP p).Fp) := (congrArg Prod.fst hwY).symm
        have e2 : (sg.e Y).2 = (w.2 : (D.s.atP p).Fp) := (congrArg Prod.snd hwY).symm
        refine ⟨by rw [e1]; exact w.1.2, by rw [e2]; exact w.2.2, (c : (D.s.atP p).Fp), c.2, ?_⟩
        rw [e1, e2]
        have hc' := congrArg Subtype.val hc
        push_cast at hc'
        first
        | linear_combination -hc'
        | (rw [← hc']; ring)
      · rintro ⟨hy1, hy2, t, ht, hteq⟩
        refine ⟨(⟨(sg.e Y).1, hy1⟩, ⟨(sg.e Y).2, hy2⟩), ?_, ?_⟩
        · show Ideal.Quotient.mk (Ideal.span {g.q}) ⟨(sg.e Y).1, hy1⟩ =
            Ideal.Quotient.mk (Ideal.span {g.q}) ⟨(sg.e Y).2, hy2⟩
          rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
          refine ⟨⟨t, ht⟩, ?_⟩
          apply Subtype.ext
          show t * (g.q : (D.s.atP p).Fp) = (sg.e Y).1 - (sg.e Y).2
          linear_combination -hteq
        · rfl
    exact key _

theorem agree_split (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hA : Agree δ M p) : ((M p).split = none ∧ (D.s.atP p).split = none) ∨
      ∃ g sg, (M p).split = some g ∧ (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
  obtain ⟨-, -, -, -, -, hm⟩ := hA
  rcases h1 : (M p).split with _ | g <;> rcases h2 : (D.s.atP p).split with _ | sg <;>
    simp only [h1, h2] at hm
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨g, sg, rfl, rfl, hm.1, hm.2⟩

theorem twisted_local_membership_iff (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hδ : δ p ≠ 0) (c : D.host.F) (hc : c ≠ 0)
    (hv : valuation (D.s.atP p).Fp ((D.s.atP p).ιF c) = valuation (D.s.atP p).Fp (δ p)) (ν s : ℕ) (t : D.host.E) :
    tMod δ p ν s t ∈ (M p).R ↔
      twist p s (algebraMap _ _ ((((D.s.atP p).ιF c) ^ ν)⁻¹) * (D.s.atP p).ιE t) *
        algebraMap _ _ (((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹) ∈ (M p).R := by
  rw [tMod_eq δ p hδ ν s t, twist_alg, mul_assoc]
  have hoth : ((oth p : ℕ) : (D.s.atP p).Fp) ≠ 0 := natFp_ne_zero p _ (oth_ne_zero p)
  have hvo : valuation (D.s.atP p).Fp ((oth p : ℕ) : (D.s.atP p).Fp) = 1 := v_nat p _ (oth_not_dvd p)
  have hc' : (D.s.atP p).ιF c ≠ 0 := (map_ne_zero _).2 hc
  exact scal_iff (D.s.atP p) ((M p).R : Set (D.s.atP p).Ep) (R_scal (M p)) _ _
    (inv_ne_zero (pow_ne_zero _ (mul_ne_zero hδ (inv_ne_zero hoth))))
    (inv_ne_zero (pow_ne_zero _ hc'))
    (by simp only [map_inv₀, map_pow, map_mul, hvo, inv_one, mul_one, hv]) _

theorem loc_iff (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (hA : Agree δ M p) (c : D.host.F) (hc : c ≠ 0)
    (hv : valuation (D.s.atP p).Fp ((D.s.atP p).ιF c) = valuation (D.s.atP p).Fp (δ p)) (ν s : ℕ) (t : D.host.E) :
    tMod δ p ν s t ∈ (M p).R ↔
      (D.s.atP p).ιE (t / algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ 1 * c ^ ν)) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((t - (-1) ^ s * D.conjF t) /
        algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ 2 * c ^ ν)) ∈ (D.s.atP p).O := by
  have hA' := hA
  obtain ⟨-, hδ, -, hO, -, -⟩ := hA'
  have hg := natFp_ne_zero p _ (gpart_ne_zero p)
  have ho := natFp_ne_zero p _ (oth_ne_zero p)
  have hvo := v_nat p _ (oth_not_dvd p)
  rw [twisted_local_membership_iff δ M p hδ c hc hv ν s t, twist_membership_iff_integral p (M p) hO (agree_split δ M p hA) s, ← gpart_mul_oth p,
    cond_gen (D.s.atP p) c ν (gpart p) (oth p) hg ho hvo 1 t,
    cond_gen (D.s.atP p) c ν (gpart p) (oth p) hg ho hvo 2, ← tw_gen (D.s.atP p)]
  simp only [pow_one]

def IsDiffGen (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) : Prop :=
  ∃ c : D.host.F, valuation (D.s.atP p).Fp ((D.s.atP p).ιF c) = valuation (D.s.atP p).Fp (δ p) ∧
    LocGen p ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (algebraMap D.host.F D.host.E c)

theorem locGen_gdd (p : PlF D) (c : D.host.F)
    (h : LocGen p ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
      (algebraMap D.host.F D.host.E c)) (k ν : ℕ) :
    LocGen p (gdd (D := D) (k : ℤ) (ν : ℤ)) (algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ k * c ^ ν)) := by
  have hgS : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    simp only [Lat.gS, Nat.cast_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
  simp only [gdd, zpow_natCast, map_mul, map_pow, map_natCast]
  exact (LocGen.span (p := p) (pow_ne_zero k hgS)).mul (h.pow ν)

theorem laIsPeriod_of (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (ν s : ℕ) : LaIsPeriod δ M ν s := by
  have key : ∀ (k : ℕ) (x : D.host.E) (p : PlF D) (c : D.host.F),
      LocGen p ((D.host.ddE : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
        (algebraMap D.host.F D.host.E c) →
      ((D.s.atP p).ιE (x / algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F) ^ k * c ^ ν)) ∈ (D.s.atP p).O ↔
        atP p (gdd (D := D) (k : ℤ) (ν : ℤ)) x) := by
    intro k x p c hc
    rw [int_iff (D.s.atP p) conjF_inv conjF_fix]
    exact ((locGen_gdd p c hc k ν).2 x).symm
  unfold LaIsPeriod
  intro t
  simp only [La, Set.mem_setOf_eq]
  rw [mem_iff_forall_atP (F := D.host.F) (gdd (D := D) 1 ν) t,
    mem_iff_forall_atP (F := D.host.F) (gdd (D := D) 2 ν) _, ← forall_and]
  apply forall_congr'
  intro p
  obtain ⟨c, hcv, hcg⟩ := hd p
  have hc0 : c ≠ 0 := fun h0 => hcg.1 (by rw [h0, map_zero])
  have k1 := key 1 t p c hcg
  have k2 := key 2 (t - (-1) ^ s * D.conjF t) p c hcg
  simp only [Nat.cast_one, Nat.cast_ofNat] at k1 k2
  rw [loc_iff δ M p (hA p) c hc0 hcv ν s t, k1, k2]

end Rec2

section Rec3

open Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices

variable {D : Formalism.BasicNotions.D7}

theorem G1root_of_agree (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) : G1root δ M := by
  intro p x
  obtain ⟨-, hδ, -, -, hpsi, -⟩ := hA p
  rw [hpsi]
  congr 1
  have hg : ((gpart p : ℕ) : (D.s.atP p).Fp) ≠ 0 := natFp_ne_zero p _ (gpart_ne_zero p)
  have hoth : ((oth p : ℕ) : (D.s.atP p).Fp) ≠ 0 := natFp_ne_zero p _ (oth_ne_zero p)
  have hu : ((uP p : ℚ) : D.host.E) = algebraMap D.host.F D.host.E (((oth p : ℕ) : D.host.F)⁻¹) := by
    rw [unitAt_eq p]
    simp [map_inv₀, map_natCast]
  have hx : x / ((Lat.gS D : ℕ) : D.host.E) = x * algebraMap D.host.F D.host.E (((Lat.gS D : ℕ) : D.host.F)⁻¹) := by
    rw [map_inv₀, map_natCast, div_eq_mul_inv]
  rw [qE_eq p, inverse_alg _ hg, hx, hu]
  simp only [map_neg, map_mul, (D.s.atP p).compat]
  simp only [map_inv₀, map_natCast]
  rw [neg_inj]
  have e : δ p * ((oth p : ℕ) : (D.s.atP p).Fp)⁻¹ * ((gpart p : ℕ) : (D.s.atP p).Fp)⁻¹ * (δ p)⁻¹ =
      ((Lat.gS D : ℕ) : (D.s.atP p).Fp)⁻¹ := by
    rw [← gpart_mul_oth p, Nat.cast_mul]
    field_simp
  rw [← e]
  simp only [map_mul]
  ring

theorem G3lat_of (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (ν s : ℕ) :
    (∀ t, t ∈ La M δ ν s ↔ t ∈ gdd (D := D) 1 ν ∧ t - (-1) ^ s * D.conjF t ∈ gdd (D := D) 2 ν) ∧
    (∀ t ∈ gdd (D := D) 2 ν, t ∈ La M δ ν s) ∧
    (∀ l ∈ dualPsiG (D := D) (La M δ ν s), l ∈ gdd (D := D) (-1) (-((ν : ℤ) + 1))) :=
  ⟨laIsPeriod_of δ M hA hd ν s, period_lattice_bounds_of_known δ M ν s (laIsPeriod_of δ M hA hd ν s)⟩

theorem global_condition_of_local_agreement (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (i : ℕ) (hi : i ≤ D.R.rS + 1) : G4 δ M i :=
  period_lattice_unramified_of_known (unramE D) δ M i hi (laIsPeriod_of δ M hA hd _ 1)

end Rec3

end Formalism.MainNotions.BridgeLemma

end
