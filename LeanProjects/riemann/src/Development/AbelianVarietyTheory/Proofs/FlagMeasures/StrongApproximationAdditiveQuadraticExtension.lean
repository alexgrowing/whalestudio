import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem int_of (T : LocAt F E sig p) (a : 𝓞 F) :
    valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a)) ≤ 1 :=
  (PlacesInt.mem_int_iff T _).2 (p.valuation_le_one a)

theorem small_local (T : LocAt F E sig p) (w : T.Fp) (hw : w ≠ 0) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a)) ≤ valuation T.Fp w := by
  haveI := T.lf
  have hw0 : valuation T.Fp w ≠ 0 := by simpa using hw
  have hn : {z : T.Fp | valuation T.Fp (z - w) < valuation T.Fp w} ∈ nhds w :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hw0, fun z hz => hz⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - w) < valuation T.Fp w := hk
  have hkv : valuation T.Fp (T.ιF k) = valuation T.Fp w := by
    have e : T.ιF k = w + (T.ιF k - w) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ hk']
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by simpa using hs0
  refine ⟨a, fun ha => ?_, ?_⟩
  · rw [ha, map_zero, zero_div, map_zero, map_zero] at hkv
    exact hw0 hkv.symm
  · have e : T.ιF (algebraMap (𝓞 F) F a) =
        T.ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) * T.ιF (algebraMap (𝓞 F) F s) := by
      rw [← map_mul, div_mul_cancel₀ _ hsK]
    rw [e, Valuation.map_mul, hkv]
    exact mul_le_of_le_one_right' (int_of T s)

theorem small (A : Places F E sig) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (w : ∀ p, (A.loc p).Fp) (hw : ∀ p ∈ S, w p ≠ 0) :
    ∃ h : 𝓞 F, h ≠ 0 ∧ ∀ p ∈ S,
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ valuation (A.loc p).Fp (w p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert q S hq ih =>
    obtain ⟨h, hh, hS⟩ := ih (fun p hp => hw p (Finset.mem_insert_of_mem hp))
    obtain ⟨a, ha, ha'⟩ := small_local (A.loc q) (w q) (hw q (Finset.mem_insert_self q S))
    refine ⟨h * a, mul_ne_zero hh ha, fun p hp => ?_⟩
    rw [map_mul, map_mul, Valuation.map_mul]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (mul_le_of_le_one_left' (int_of _ h)).trans ha'
    · exact (mul_le_of_le_one_right' (int_of _ a)).trans (hS p hp)

theorem approx_local (T : LocAt F E sig p) (z : T.Fp) (hz : valuation T.Fp z ≤ 1) (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, valuation T.Fp (z - T.ιF (algebraMap (𝓞 F) F a)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := by
  haveI := T.lf
  have hhK : algebraMap (𝓞 F) F h ≠ 0 := by simpa using hh
  have hh0 : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) ≠ 0 := by simpa using hhK
  have hn : {x : T.Fp | valuation T.Fp (x - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))} ∈ nhds z :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hh0, fun x hx => hx⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := hk
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← PlacesInt.mem_int_iff T]
    have e : T.ιF k = (T.ιF k - z) + z := by ring
    show valuation T.Fp (T.ιF k) ≤ 1
    rw [e]
    exact (valuation T.Fp).map_add_le (hk'.le.trans (int_of T h)) hz
  have hpv : p.valuation F (algebraMap (𝓞 F) F h) ≠ 0 := by simpa using hhK
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hpv)
  refine ⟨a, ?_⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - k)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) :=
    (PlacesInt.val_le_iff T _ _).2 ha.le
  have e : z - T.ιF (algebraMap (𝓞 F) F a) = -(T.ιF k - z) - T.ιF (algebraMap (𝓞 F) F a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine ((valuation T.Fp).map_sub _ _).trans (max_le ?_ ha')
  rw [Valuation.map_neg]; exact hk'.le

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem approx (A : Places F E sig) (z : ∀ p, (A.loc p).Fp) (hz : ∀ p, valuation (A.loc p).Fp (z p) ≤ 1)
    (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, ∀ p, valuation (A.loc p).Fp (z p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) ≤
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) := by
  have hT : {p : HeightOneSpectrum (𝓞 F) | p.asIdeal ∣ Ideal.span {h}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hh)
  choose a0 ha0 using fun p => approx_local (A.loc p) (z p) (hz p) h hh
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hT.toFinset) (fun p => p.asIdeal)
    (fun p => multiplicity p.asIdeal (Ideal.span {h})) (fun p _ => p.prime)
    (fun p _ q _ hpq e => hpq (HeightOneSpectrum.ext e)) (fun p => a0 p.1)
  refine ⟨a, fun p => ?_⟩
  by_cases hp : p ∈ hT.toFinset
  · have h1 := ha p hp
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity p hh,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)] at h1
    have h2 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h1
    have e : z p - (A.loc p).ιF (algebraMap (𝓞 F) F a) =
        (z p - (A.loc p).ιF (algebraMap (𝓞 F) F (a0 p))) - (A.loc p).ιF (algebraMap (𝓞 F) F (a - a0 p)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (ha0 p) h2)
  · have h1 : p.intValuation h = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hp ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    have h2 : p.valuation F (algebraMap (𝓞 F) F 1) ≤ p.valuation F (algebraMap (𝓞 F) F h) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, h1, map_one]
    have h3 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h2
    rw [map_one, map_one, map_one] at h3
    refine le_trans ?_ h3
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (hz p) (int_of _ a))

theorem approxF (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Fp) (hy : {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite) :
    ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o := by

  obtain ⟨r, hr, hr'⟩ := small A hy.toFinset (fun p => (y p)⁻¹) (fun p hp => by
    have hp' : y p ∉ 𝒪[(A.loc p).Fp] := hy.mem_toFinset.mp hp
    exact inv_ne_zero fun h0 => hp' (h0 ▸ zero_mem _))
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by simpa using hr
  have hz : ∀ p, valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p) ≤ 1 := by
    intro p
    rw [Valuation.map_mul]
    by_cases hp : y p ∈ 𝒪[(A.loc p).Fp]
    · exact mul_le_one' (int_of _ r) hp
    · have h1 := hr' p (hy.mem_toFinset.mpr hp)
      have hy0 : y p ≠ 0 := fun h0 => hp (h0 ▸ zero_mem _)
      have hy1 : valuation (A.loc p).Fp (y p) ≠ 0 := by simpa using hy0
      rw [map_inv₀] at h1
      calc _ ≤ (valuation (A.loc p).Fp (y p))⁻¹ * valuation (A.loc p).Fp (y p) := mul_le_mul' h1 le_rfl
        _ = 1 := inv_mul_cancel₀ hy1

  have hr0 : {p : HeightOneSpectrum (𝓞 F) | p.valuation F (algebraMap (𝓞 F) F r) < 1}.Finite := by
    refine (HeightOneSpectrum.Support.finite (𝓞 F) (algebraMap (𝓞 F) F r)⁻¹).subset fun p hp => ?_
    have hp' : p.valuation F (algebraMap (𝓞 F) F r) < 1 := hp
    show 1 < p.valuation F (algebraMap (𝓞 F) F r)⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hrK), hp'⟩
  obtain ⟨h, hh, hh'⟩ := small A (hc.union hr0).toFinset
    (fun p => (A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) (fun p _ => mul_ne_zero (by simpa using hrK) (c p).ne_zero)
  obtain ⟨a, ha⟩ := approx A _ hz h hh
  refine ⟨algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r, fun p => ?_⟩
  set v := valuation (A.loc p).Fp
  have hrp : (A.loc p).ιF (algebraMap (𝓞 F) F r) ≠ 0 := by simpa using hrK
  have hvr : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) ≠ 0 := by simpa using hrp
  have hcv : v (c p : (A.loc p).Fp) ≠ 0 := by simpa using (c p).ne_zero

  have key : v ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) := by
    by_cases hp : p ∈ (hc.union hr0).toFinset
    · exact hh' p hp
    · rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hp
      obtain ⟨u, hu⟩ := not_not.mp hp.1
      have hu1 : v (c p : (A.loc p).Fp) = 1 := by
        rw [← hu]
        exact (Valuation.integer.integers v).one_of_isUnit u.isUnit
      have hr1 : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) = 1 := by
        refine le_antisymm (int_of _ r) ?_
        have := (PlacesInt.val_le_iff (A.loc p) 1 (algebraMap (𝓞 F) F r)).2 (not_lt.mp hp.2 |>.trans_eq' (by simp))
        simpa using this
      rw [Valuation.map_mul, hu1, hr1, mul_one]
      exact int_of _ h
  set d := (A.loc p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r) - y p
  have hd : d = -((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) *
      ((A.loc p).ιF (algebraMap (𝓞 F) F r))⁻¹ := by
    simp only [d, map_div₀]; field_simp; ring
  have hdv : v d ≤ v (c p : (A.loc p).Fp) := by
    rw [hd, Valuation.map_mul, Valuation.map_neg, map_inv₀]
    have := (ha p).trans key
    rw [Valuation.map_mul] at this
    calc _ ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) * v (c p : (A.loc p).Fp) *
          (v ((A.loc p).ιF (algebraMap (𝓞 F) F r)))⁻¹ := mul_le_mul' this le_rfl
      _ = v (c p : (A.loc p).Fp) := by field_simp
  refine ⟨⟨(c p : (A.loc p).Fp)⁻¹ * d, ?_⟩, ?_⟩
  · show v ((c p : (A.loc p).Fp)⁻¹ * d) ≤ 1
    rw [Valuation.map_mul, map_inv₀]
    calc _ ≤ (v (c p : (A.loc p).Fp))⁻¹ * v (c p : (A.loc p).Fp) := mul_le_mul' le_rfl hdv
      _ = 1 := inv_mul_cancel₀ hcv
  · show d = c p * ((c p : (A.loc p).Fp)⁻¹ * d)
    rw [← mul_assoc, mul_inv_cancel₀ (c p).ne_zero, one_mul]

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := exists_place F
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem sig_ne (A : Places F E sig) : ∃ e : E, sig e ≠ e := by
  by_contra hne
  push_neg at hne
  obtain ⟨p⟩ := exists_place F
  have h2 : ∀ z, (A.loc p).cj z = z := by
    intro z
    have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
      rw [(A.loc p).span]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, hne]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
    intro z
    exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
  have h4 := LinearMap.finrank_le_finrank_of_surjective h3
  rw [(A.loc p).rank, Module.finrank_self] at h4
  omega

theorem exists_d (A : Places F E sig) : ∃ d : 𝓞 E, sig (d : E) = -(d : E) ∧ (d : E) ≠ 0 := by
  have hint : ∀ o : 𝓞 E, IsIntegral ℤ (sig (o : E)) := fun o =>
    (o.isIntegral_coe).map (sig.toRingHom.toIntAlgHom)
  suffices h : ∃ o : 𝓞 E, sig (o : E) ≠ o by
    obtain ⟨o, ho⟩ := h
    refine ⟨o - ⟨sig o, hint o⟩, ?_, ?_⟩
    · change sig ((o : E) - sig o) = -((o : E) - sig o)
      rw [map_sub, sig_sig A]; ring
    · change (o : E) - sig o ≠ 0
      rw [sub_ne_zero]
      exact fun h => ho h.symm
  by_contra hne
  push_neg at hne
  obtain ⟨e, he⟩ := sig_ne A
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  apply he
  rw [map_div₀]
  exact congrArg₂ (· / ·) (hne a) (hne s)

theorem mem_int_of_O (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (w : (A.loc p).Fp)
    (h : algebraMap (A.loc p).Fp (A.loc p).Ep w ∈ (A.L p).O) : w ∈ 𝒪[(A.loc p).Fp] := by
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  rw [(A.L p).O_def] at h
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] w :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h
  exact Valuation.Integers.mem_of_integral (Valuation.integer.integers (valuation (A.loc p).Fp)) h2

theorem O_of_int (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (o : 𝒪[(A.loc p).Fp]) :
    algebraMap (A.loc p).Fp (A.loc p).Ep (o : (A.loc p).Fp) ∈ (A.L p).O := by
  rw [(A.L p).O_def]
  exact (isIntegral_algebraMap (x := o)).algebraMap

theorem cj_mem (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep)
    (h : y ∈ (A.L p).O) : (A.L p).cj y ∈ (A.L p).O := by
  rw [(A.L p).O_def] at h ⊢
  exact h.map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem decomp (A : Places F E sig) (d : E) (hd : sig d = -d) (hd0 : d ≠ 0) (p : HeightOneSpectrum (𝓞 F))
    (y : (A.loc p).Ep) : ∃ a b : (A.loc p).Fp,
      y = algebraMap _ _ a + algebraMap _ _ b * (A.loc p).ιE d ∧
      algebraMap _ _ a = (A.loc p).ιE (algebraMap F E 2⁻¹) * (y + (A.L p).cj y) ∧
      (y ∈ (A.L p).O → (A.loc p).ιE d⁻¹ ∈ (A.L p).O → (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] →
        a ∈ 𝒪[(A.loc p).Fp] ∧ b ∈ 𝒪[(A.loc p).Fp]) := by
  have cjE : ∀ x, (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
    intro x; rw [A.L_cj]; exact (A.loc p).cj_ιE x
  obtain ⟨u, hu⟩ := ((A.L p).cj_fix (y + (A.L p).cj y)).1 (by rw [map_add, (A.L p).cj_cj, add_comm])
  obtain ⟨w, hw⟩ := ((A.L p).cj_fix ((y - (A.L p).cj y) * (A.loc p).ιE d⁻¹)).1 (by
    rw [map_mul, map_sub, (A.L p).cj_cj, cjE, map_inv₀, hd, inv_neg, map_neg]; ring)
  have hh : algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF 2⁻¹) = (A.loc p).ιE (algebraMap F E 2⁻¹) :=
    ((A.loc p).compat _).symm
  have e1 : (A.loc p).ιE d⁻¹ * (A.loc p).ιE d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
  have e2 : (A.loc p).ιE (algebraMap F E 2⁻¹) * 2 = 1 := by
    have : algebraMap F E 2⁻¹ * 2 = 1 := by
      rw [map_inv₀, map_ofNat]; exact inv_mul_cancel₀ two_ne_zero
    rw [← map_ofNat (A.loc p).ιE 2, ← map_mul, this, map_one]
  refine ⟨u * (A.loc p).ιF 2⁻¹, w * (A.loc p).ιF 2⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, hu, hw, hh]
    linear_combination (-((A.loc p).ιE (algebraMap F E 2⁻¹) * (y - (A.L p).cj y))) * e1 + (-y) * e2
  · rw [map_mul, hu, hh, mul_comm]
  · intro hy hdi h2i
    have hcy := cj_mem A p y hy
    refine ⟨mul_mem (mem_int_of_O A p u (hu ▸ add_mem hy hcy)) h2i,
      mul_mem (mem_int_of_O A p w (hw ▸ mul_mem (sub_mem hy hcy) hdi)) h2i⟩

theorem fin_two (A : Places F E sig) :
    {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]}.Finite := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) (2⁻¹ : F)).subset fun p hp => ?_
  have hp' : ¬ (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] := hp
  rw [PlacesInt.mem_int_iff, not_le] at hp'
  exact hp'

theorem approxE (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Ep) (hy : {p | y p ∉ (A.L p).O}.Finite) :
    ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  obtain ⟨d, hd, hd0⟩ := exists_d A
  have hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O := (PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩
  have hdi := (PlacesInt.integers_local A).2.1 (d : E)⁻¹
  choose a b hab _ hint using fun p => decomp A d hd hd0 p (y p)
  have hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪
      {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} →
      a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp] := by
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    exact hint p hp.1.1 hp.1.2 hp.2
  have hfin := (hy.union hdi).union (fin_two A)
  obtain ⟨α, hα⟩ := approxF A c hc a (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).1)
  obtain ⟨β, hβ⟩ := approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)
  refine ⟨algebraMap F E α + algebraMap F E β * d, fun p => ?_⟩
  obtain ⟨o1, ho1⟩ := hα p
  obtain ⟨o2, ho2⟩ := hβ p
  refine ⟨algebraMap _ _ (o1 : (A.loc p).Fp) + algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d,
    add_mem (O_of_int A p o1) (mul_mem (O_of_int A p o2) (hdO p)), ?_⟩
  have e1 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho1
  have e2 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2
  rw [map_sub, map_mul] at e1 e2
  rw [map_add, map_mul, (A.loc p).compat, (A.loc p).compat]
  linear_combination e1 + (A.loc p).ιE d * e2 - hab p

theorem approxTr (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (t : E) (y : ∀ p, (A.loc p).Ep) (hy : {p | y p ∉ (A.L p).O}.Finite)
    (hyt : ∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) :
    ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  obtain ⟨d, hd, hd0⟩ := exists_d A
  have hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O := (PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩
  have hdi := (PlacesInt.integers_local A).2.1 (d : E)⁻¹
  have ht : sig t = t := by
    obtain ⟨p⟩ := exists_place F
    haveI := PlacesInt.nontrivial_Ep (A.loc p)
    apply (A.loc p).ιE.injective
    rw [← (A.loc p).cj_ιE, ← A.L_cj, ← hyt p, map_add, (A.L p).cj_cj, add_comm]
  choose a b hab hA hint using fun p => decomp A d hd hd0 p (y p)
  have hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪
      {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} →
      a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp] := by
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    exact hint p hp.1.1 hp.1.2 hp.2
  have hfin := (hy.union hdi).union (fin_two A)
  obtain ⟨β, hβ⟩ := approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)
  refine ⟨algebraMap F E 2⁻¹ * t + algebraMap F E β * d, ?_, fun p => ?_⟩
  · rw [map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, ht, hd, map_inv₀, map_ofNat]
    field_simp
    ring
  obtain ⟨o2, ho2⟩ := hβ p
  refine ⟨algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d, mul_mem (O_of_int A p o2) (hdO p), ?_⟩
  have e2 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2
  rw [map_sub, map_mul] at e2
  rw [map_add, map_mul, map_mul, (A.loc p).compat β]
  linear_combination (A.loc p).ιE d * e2 - hab p - hA p - (A.loc p).ιE (algebraMap F E 2⁻¹) * hyt p

theorem strong_approx_additive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → (∀ y : ∀ p, (A.loc p).Fp, {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite → ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o) ∧ (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o) ∧ ∀ (t : E) (y : ∀ p, (A.loc p).Ep), {p | y p ∉ (A.L p).O}.Finite → (∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) → ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A c hc
  exact ⟨fun y hy => approxF A c hc y hy, fun y hy => approxE A c hc y hy,
    fun t y hy hyt => approxTr A c hc t y hy hyt⟩

end GlobalTheory.HL.StrongApprox
