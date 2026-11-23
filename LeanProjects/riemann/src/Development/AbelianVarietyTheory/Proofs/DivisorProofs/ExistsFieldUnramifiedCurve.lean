import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension

set_option autoImplicit false

namespace GlobalTheory.RefSum.UnramCurveField

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

theorem not_dvd_discr_of_unramIn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {n q : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) (hK : ¬ (q : ℤ) ∣ discr K)
    (hL : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → GlobalTheory.NT.UnramIn L 𝔭) :
    ¬ (q : ℤ) ∣ discr L := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem L (𝓞 L) hqz).2 fun P hP hqP => ?_
  have hqp : ((q : ℤ) : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.mem_under, map_intCast]; exact hqP
  have hp0 : P.under (𝓞 K) ≠ ⊥ := fun e => by
    rw [e, Ideal.mem_bot] at hqp
    exact hq.ne_zero (by exact_mod_cast hqp)
  have h1 : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 K)) :=
    (not_dvd_discr_iff_forall_mem K (𝓞 K) hqz).1 hK _ inferInstance hqp
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, hp0⟩
  have hnd : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    intro hnp
    obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
    have h2 : ((a * q + b * n : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
      exact add_mem (Ideal.mul_mem_left _ _ hqp) (Ideal.mul_mem_left _ _ (by rwa [Int.cast_natCast]))
    rw [hab, Int.cast_one] at h2
    exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have : P.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  have h3 : Algebra.IsUnramifiedAt (𝓞 K) P := GlobalTheory.NT.isUnramifiedAt_of_unramIn (hL 𝔭 hnd) P
  exact Algebra.IsUnramifiedAt.comp (P.under (𝓞 K)) P

theorem exists_field_of_rayField (hRF : GlobalTheory.NT.RayField) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ) (hn : 3 ≤ n) (hq : q.Prime) (hqn : ¬ q ∣ n) (hqd : ¬ q ∣ H.d) :
    ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hdR : ¬ (q : ℤ) ∣ discr R :=
    not_dvd_discr_of_unramIn K₀ R hq hqn (by rwa [hD, dvd_neg, Int.natCast_dvd_natCast]) hR.1
  refine ⟨R.restrictScalars ℚ, hNR, hdR, ?_⟩
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H _ n (by omega)).1
    (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀)) fun P hP => ?_
  have hW := GlobalTheory.FieldSize.InRayAny.weberSet_subset K₀ h2 (by omega) P (fun z => ?_) n hn R hR
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem exists_unram_curveOver : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n :=
  fun h E _ _ _ H n q hn hq hnd => exists_field_of_rayField h.p8 E H n q hn hq
    (fun e => hnd ((e.mul_left 2).mul_right _)) (fun e => hnd (e.mul_left _))

end GlobalTheory.RefSum.UnramCurveField
