import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamData
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRingOfIntegersLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigRam

open NumberField IsLocalRing UniqueFactorizationMonoid Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem exists_pairs_sides {Ty Pl : Type} [Fintype Ty] (pl : Ty → Pl) (cj : Pl → Pl) (hcj : ∀ w, cj (cj w) = w)
    (hne : ∀ t, cj (pl t) ≠ pl t) :
    ∃ (c : Ty → Finset Ty) (s : Ty → Bool), ∀ t t', pl t' = cj (pl t) → c t = c t' ∧ s t ≠ s t' := by
  classical
  letI : LinearOrder Pl := linearOrderOfSTO WellOrderingRel
  refine ⟨fun t => Finset.univ.filter fun x => pl x = pl t ∨ pl x = cj (pl t),
    fun t => decide (pl t < cj (pl t)), fun t t' h => ⟨?_, ?_⟩⟩
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, hcj]
    exact or_comm
  · simp only [h, hcj]
    rcases lt_or_gt_of_ne (hne t) with h1 | h1
    · simp [h1, h1.not_gt]
    · simp [h1, h1.not_gt]

theorem exists_delta {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (σ : 𝓞 E →+* V) (p a m : ℕ) (hp : p.Prime) (hpV : ¬ IsUnit (p : V)) (hm : ¬ p ∣ m)
    (hd : (discr E).natAbs = p ^ a * m) :
    ∃ δ ∈ differentIdeal ℤ (𝓞 E), σ δ ^ Module.finrank ℚ E ∣ (p : V) ^ a := by
  classical
  set P : Ideal (𝓞 E) := (maximalIdeal V).comap σ with hP
  have hPp : P.IsPrime := Ideal.comap_isPrime σ _
  have hpP : (p : 𝓞 E) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hpV
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h] at hpP
    exact hp0 ((Submodule.mem_bot _).1 hpP)
  haveI : P.IsMaximal := hPp.isMaximal hP0
  have hexp := diffExp E p a m hp hm hd P hPp hpP
  obtain ⟨Q, hQ, hD⟩ := Ideal.eq_prime_pow_mul_coprime (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E)) P
  obtain ⟨Q', -, hI⟩ := Ideal.eq_prime_pow_mul_coprime
    (I := Ideal.span {(p : 𝓞 E)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) P
  have hQm : Q.map σ = ⊤ := by
    by_contra h
    have h1 : Q.map σ ≤ maximalIdeal V := le_maximalIdeal h
    have h2 : Q ≤ P := Ideal.map_le_iff_le_comap.1 h1
    exact hPp.ne_top (by rw [← hQ, sup_eq_left.2 h2])
  obtain ⟨δ, hδ, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min
    ((fun x => IsDiscreteValuationRing.addVal V (σ x)) '' (differentIdeal ℤ (𝓞 E) : Set (𝓞 E)))
    ⟨_, 0, zero_mem _, rfl⟩
  obtain ⟨δ, hδ, rfl⟩ := hδ
  refine ⟨δ, hδ, ?_⟩
  have hle : (differentIdeal ℤ (𝓞 E)).map σ ≤ Ideal.span {σ δ} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd]
    exact not_lt.1 (hmin _ ⟨x, hx, rfl⟩)
  have h1 : (p : 𝓞 E) ∈ P ^ (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P := by
    have h0 : Ideal.span {(p : 𝓞 E)} ≤ P ^ (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P :=
      Ideal.le_of_dvd (Dvd.intro _ hI.symm)
    exact h0 (Ideal.mem_span_singleton_self _)
  have h2 := Ideal.mem_map_of_mem σ (Ideal.pow_mem_pow h1 a)
  rw [← pow_mul, mul_comm, ← hexp, pow_mul, Ideal.map_pow, map_pow, map_natCast] at h2
  have h3 : (P ^ (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P).map σ = (differentIdeal ℤ (𝓞 E)).map σ := by
    conv_rhs => rw [hD]
    rw [Ideal.map_mul, hQm, Ideal.mul_top]
  rw [h3] at h2
  have h4 := Ideal.pow_right_mono hle _ h2
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4

theorem vV_pow {V k : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field k] [Algebra V k]
    [IsFractionRing V k] (x : k) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV, map_pow, WithZero.log_pow]

theorem bound_of_den {V k : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field k] [Algebra V k]
    [IsFractionRing V k] (r q : V) (hq : q ≠ 0) (n a : ℕ) (hn : 0 < n) (hdvd : r ^ n ∣ q ^ a) (x : k)
    (hx : algebraMap V k r * x ∈ (algebraMap V k).range) (e : ℕ) :
    (((-((vV V (algebraMap V k q) : ℝ) / e * ((a : ℝ) / n))) : ℝ) : EReal) ≤ nval V e x := by
  by_cases hx0 : x = 0
  · rw [hx0, nval_zero]; exact le_top
  have hinj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  obtain ⟨t, ht⟩ := hdvd
  have hqa : q ^ a ≠ 0 := pow_ne_zero _ hq
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hqa
    rw [ht, zero_pow hn.ne', zero_mul]
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hqa (by rw [ht, mul_zero])
  have hrk : algebraMap V k r ≠ 0 := (map_ne_zero_iff _ hinj).2 hr0
  have h1 : (a : ℤ) * vV V (algebraMap V k q) = n * vV V (algebraMap V k r) + vV V (algebraMap V k t) := by
    rw [← vV_pow, ← vV_pow, ← vV_mul (pow_ne_zero _ hrk) ((map_ne_zero_iff _ hinj).2 ht0), ← map_pow, ← map_pow,
      ← map_mul, ht]
  have h2 := ERam.vV_alg_nonneg (k := k) t
  obtain ⟨v, hv⟩ := hx
  have h3 := ERam.vV_alg_nonneg (k := k) v
  rw [hv, vV_mul hrk hx0] at h3
  have h4 : -((a : ℤ) * vV V (algebraMap V k q)) ≤ n * vV V x := by nlinarith
  have h5 : -((a : ℝ) * (vV V (algebraMap V k q) : ℝ)) ≤ n * (vV V x : ℝ) := by exact_mod_cast h4
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [nval_of_ne hx0, EReal.coe_le_coe_iff]
  have h6 : -((vV V (algebraMap V k q) : ℝ) * ((a : ℝ) / n)) ≤ (vV V x : ℝ) := by
    rw [← mul_div_assoc, ← neg_div, div_le_iff₀ hn']
    linarith
  have h7 := div_le_div_of_nonneg_right h6 (Nat.cast_nonneg (α := ℝ) e)
  refine le_trans (le_of_eq ?_) h7
  ring

theorem isRQ_of_nonunit {V k : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [Field k]
    [Algebra V k] [Algebra ℚ k] [IsFractionRing V k] (N : ℕ) (hN0 : N ≠ 0) (hNu : ¬ IsUnit (N : V)) :
    TB.IsRQ (R := V) k := by
  refine ⟨IsFractionRing.injective V k, fun y => ?_⟩
  have hNV0 : (N : V) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
  have hϖN : ϖ ∣ (N : V) := by
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := V) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
  obtain ⟨t, ht⟩ : s ∣ (N : V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
  refine ⟨t * a, N ^ n, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), ?_⟩
  have hsk : algebraMap V k s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V k)).2 hs0
  have h1 : ((N ^ n : ℕ) : k) = algebraMap V k s * algebraMap V k t := by
    rw [← map_mul, ← ht, map_pow, map_natCast, Nat.cast_pow]
  rw [h1, map_mul]
  field_simp

theorem isIntegral_mul_dual {E : Type} [Field E] [NumberField E] (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E))
    (i : Fin (ERam.nI E)) : IsIntegral ℤ ((δ : E) * ERam.omDF (E := E) i) := by
  classical
  have hbqω : ∀ i, integralBasis E i = algebraMap (𝓞 E) E (RingOfIntegers.basis E i) :=
    fun i => integralBasis_apply E i
  refine _root_.dual_difference E _ (integralBasis E) (fun i => ?_) (fun x => ?_) _ hδ _
  · rw [hbqω]
    exact RingOfIntegers.isIntegral_coe _
  · refine ⟨fun i => (RingOfIntegers.basis E).repr x i, ?_⟩
    have h1 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr x)
    rw [map_sum] at h1
    show algebraMap (𝓞 E) E x = _
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbqω, map_zsmul, Int.cast_smul_eq_zsmul]

theorem sum_embeddings {E : Type} [Field E] [NumberField E] (x : E) :
    ∑ τ : E →+* ℂ, τ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun τ => rfl

end GlobalTheory.EigRam

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

open GlobalTheory.EigRam ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf in

theorem GlobalTheory.PlaceInt.exists_ramified_eigenLifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → letI := io.toAlgebra; ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (cc : (E →+* ℂ) → π) (s : (E →+* ℂ) → Bool), (∀ τ, cc (ComplexEmbedding.conjugate τ) = cc τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧ ∃ (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr), (∀ ℓ i, (((-((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E))) : ℝ) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧ (∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 → ∑ i, (algebraMap T.V T.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (0, ψ ℓ)) := by
  classical
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpV hm hd hmove e _
  letI := io.toAlgebra
  obtain ⟨B, hB, hall⟩ := integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hc, -, heig0, -⟩ := hall B hB
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hRQ : TB.IsRQ (R := T.V) T.Fr := isRQ_of_nonunit p hp.ne_zero hpV
  have huv : ∀ ℓ, C.ch.uvec ℓ = fun i => algebraMap T.V T.Fr (C.uvecT ℓ i) :=
    fun ℓ => funext (C.gen.1.2.2.2.2.2.2 ℓ)
  let ψ : (E →+* ℂ) → E →+* T.Fr := fun τ => io.comp (embF c τ)
  let χ : (E →+* ℂ) → 𝓞 E →+* T.Fr := fun τ => (ψ τ).comp (algebraMap (𝓞 E) E)
  choose σ hσ using fun τ => exists_ringOfIntegers_lift E T.V T.Fr (ψ τ)
  have hconj : ∀ (τ : E →+* ℂ) (x : 𝓞 E), χ (ComplexEmbedding.conjugate τ) x = χ τ (star x) := by
    intro τ x
    show io (embK c _ x) = io (embK c τ (star x))
    congr 1
    apply Subtype.ext
    show ((embK c _ x : c.F) : ℂ) = ((embK c τ (star x) : c.F) : ℂ)
    rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, hstar, H.bar_eq,
      NumberField.IsCMField.complexEmbedding_complexConj]
  have hχinj : ∀ t t', t ≠ t' → ∃ a, χ t a ≠ χ t' a := by
    intro t t' hne
    by_contra hall
    push Not at hall
    apply hne
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
    exact congrArg (fun z : c.F => (z : ℂ)) (io.injective (hall x))
  have hχsep : ∀ t t', t' ≠ ComplexEmbedding.conjugate t → ∃ a, χ t a ≠ χ t' (star a) := by
    intro t t' hne
    obtain ⟨a, ha⟩ := hχinj _ _ hne
    refine ⟨star a, ?_⟩
    rw [star_star, ← hconj]
    exact ha.symm
  have htr : ∀ x : E, ∑ t, ψ t x = ((Algebra.trace ℚ E x : ℚ) : T.Fr) := by
    intro x
    have h1 : ∑ t, embF c t x = ((Algebra.trace ℚ E x : ℚ) : c.F) := by
      apply (algebraMap c.F ℂ).injective
      rw [map_sum, map_ratCast, ← sum_embeddings]
      rfl
    have h2 := congrArg io h1
    rw [map_sum, map_ratCast] at h2
    exact h2
  have hNmem : (((discr E).natAbs : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
    have h1 := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
    rwa [NumberField.absNorm_differentIdeal (K := E)] at h1
  have hN0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hNint := isIntegral_mul_dual _ hNmem
  let pl : (E →+* ℂ) → Ideal (𝓞 E) := fun τ => (maximalIdeal T.V).comap (σ τ)
  let cjP : Ideal (𝓞 E) → Ideal (𝓞 E) := fun I => I.comap (starRingEnd (𝓞 E))
  have hσc : ∀ τ x, σ (ComplexEmbedding.conjugate τ) x = σ τ (star x) := by
    intro τ x
    apply hinj
    rw [hσ, hσ]
    exact hconj τ x
  have hpl : ∀ t, pl (ComplexEmbedding.conjugate t) = cjP (pl t) := by
    intro t
    ext x
    simp only [pl, cjP, Ideal.mem_comap, hσc, starRingEnd_apply]
  have hcj : ∀ w, cjP (cjP w) = w := by
    intro w
    ext x
    simp only [cjP, Ideal.mem_comap, starRingEnd_apply, star_star]
  have hplp : ∀ t, (pl t).IsPrime := fun t => Ideal.comap_isPrime _ _
  have hpmem : ∀ t, (p : 𝓞 E) ∈ pl t := by
    intro t
    show σ t (p : 𝓞 E) ∈ maximalIdeal T.V
    rw [map_natCast]
    exact hpV
  have hpl0 : ∀ t, pl t ≠ ⊥ := by
    intro t h
    have := hpmem t
    rw [h] at this
    exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 this)
  have hne : ∀ t, cjP (pl t) ≠ pl t := by
    intro t h
    obtain ⟨x, hx, hx'⟩ := hmove _ (hplp t) (hpmem t)
    rw [← h] at hx
    rw [← hstar] at hx'
    exact hx' hx
  obtain ⟨cc, s, hpair⟩ := exists_pairs_sides pl cjP hcj hne
  have hplace : ∀ w : Ideal (𝓞 E), ∃ (n : ℕ) (b : Fin n → 𝓞 E) (a : Fin n → T.V), ∀ t,
      ERam.evD (χ t) b (fun i => algebraMap T.V T.Fr (a i)) = if pl t = w then 1 else 0 := by
    intro w
    by_cases hw : ∃ t, pl t = w
    · obtain ⟨t0, rfl⟩ := hw
      obtain ⟨n, b, a, h⟩ := placeIdem E T.V T.Fr (pl t0) (hplp t0) (hpl0 t0)
      refine ⟨n, b, a, fun t => (h (ψ t)).trans (if_congr ?_ rfl rfl)⟩
      have hmem : ∀ x : 𝓞 E, ψ t (x : E) ∈ algebraMap T.V T.Fr '' (maximalIdeal T.V : Set T.V) ↔ x ∈ pl t := by
        intro x
        rw [← hσ, hinj.mem_set_image]
        rfl
      simp only [hmem]
      exact ⟨fun h' => Ideal.ext fun x => (h' x).symm, fun h' x => by rw [h']⟩
    · refine ⟨0, Fin.elim0, Fin.elim0, fun t => ?_⟩
      rw [if_neg fun h => hw ⟨t, h⟩]
      simp [ERam.evD]
  choose nP bP aP hP using hplace
  choose δ hδ hδv using fun τ => exists_delta (σ τ) p a m hp hpV hm hd
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hδ0 : ∀ τ, ψ τ (δ τ : E) ≠ 0 := by
    intro τ h
    rw [← hσ, map_eq_zero_iff _ hinj] at h
    have h2 := hδv τ
    rw [h, zero_pow hn.ne', zero_dvd_iff] at h2
    exact pow_ne_zero _ hp0 h2
  obtain ⟨φ, ψ', h1, h2, h3, h4, h5⟩ := ERam.eigLiftRam_core hRQ B (gaugeOf C) hc (fun ℓ : Lt1 Dw => ℓ.1) χ
    ComplexEmbedding.conjugate hχsep hχinj C.uvecT (fun ℓ a => by rw [← huv]; exact heig0 ℓ a)
    (fun _ => ERam.nI E) (fun _ => ERam.bD _ hNint) (fun t => ERam.cD (ψ t) _) (fun t => ERam.eqv_D _ _ hNint)
    (ERam.comp_D ψ (fun x => by rw [htr, eq_ratCast]) _ hN0 hNint _)
    (ERam.comp_D ψ (fun x => by rw [htr, eq_ratCast]) _ hN0 hNint _)
    pl cjP hpl nP bP aP (fun w t => by convert hP w t)
    (fun _ => ERam.nI E) (fun t => ERam.bD _ (isIntegral_mul_dual _ (hδ t))) (fun t => ERam.cD (ψ t) (δ t))
    (fun t => ERam.eqv_D _ _ _) (fun t => ERam.ev_D _ _ _ (hδ0 t)) (fun t => σ t (δ t))
    (fun t i => ⟨σ t (ERam.omF i), by
      rw [hσ, hσ, ERam.cD, mul_div_cancel₀ _ (hδ0 t)]⟩) cc s hpair
  refine ⟨Finset (E →+* ℂ), inferInstance, inferInstance, cc, s, fun τ => ?_, φ, ψ', fun ℓ i => ?_, ?_⟩
  · obtain ⟨e1, e2⟩ := hpair τ _ (hpl τ)
    exact ⟨e1.symm, e2.symm⟩
  · have := bound_of_den (k := T.Fr) _ _ hp0 _ a hn (hδv ℓ.1) _ (h1 ℓ i) e
    rwa [map_natCast] at this
  · simp only [huv]
    exact ⟨h2, h3, h4, h5⟩
