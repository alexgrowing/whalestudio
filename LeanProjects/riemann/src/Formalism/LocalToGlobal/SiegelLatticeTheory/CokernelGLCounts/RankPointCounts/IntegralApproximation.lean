import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.IntegralApproximation

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem v_le_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x y : F) :
    valuation L.Fp (L.ιF x) ≤ valuation L.Fp (L.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← Valuation.Compatible.vle_iff_le]
  exact L.val x y

theorem v_le_one_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x : F) :
    valuation L.Fp (L.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := by
  have h := v_le_iff L x 1
  simpa only [map_one] using h

theorem v_lt_one_iff (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) (x : F) :
    valuation L.Fp (L.ιF x) < 1 ↔ p.valuation F x < 1 := by
  rw [← not_le, ← not_le]
  have h := v_le_iff L 1 x
  simp only [map_one] at h
  rw [h]

theorem exists_int_approx (x : F) (hx : p.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, p.valuation F (x - algebraMap (𝓞 F) F a) < 1 := by
  classical
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 F)) x
  dsimp only at hx ⊢
  have hs0 : (s : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hvs : p.intValuation (s : 𝓞 F) ≠ 0 := p.intValuation_ne_zero _ hs0
  rw [HeightOneSpectrum.valuation_of_mk', div_le_one₀ (zero_lt_iff.mpr hvs)] at hx
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  have htop : p.asIdeal ≠ ⊤ := p.isPrime.ne_top
  have hex : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hs0
    have hmem : (s : 𝓞 F) ∈ ⨅ i, p.asIdeal ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      cases i with
      | zero => simp
      | succ n => exact h n
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ htop] at hmem
    exact (Ideal.mem_bot).1 hmem
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, (s : 𝓞 F) ∉ p.asIdeal ^ (n + 1) ∧ (s : 𝓞 F) ∈ p.asIdeal ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have hm := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      rw [not_not, Nat.sub_add_cancel hpos] at hm
      exact hm
  have hb : b ∈ p.asIdeal ^ n := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at hn ⊢
    exact hx.trans hn
  have hI : Ideal.span {(s : 𝓞 F)} ⊔ p.asIdeal ^ (n + 1) = p.asIdeal ^ n := by
    apply Ideal.eq_prime_pow_of_succ_lt_of_le hp0
    · refine lt_of_le_of_ne le_sup_right fun h => hn1 ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hn) (Ideal.pow_le_pow_right (Nat.le_succ n))
  rw [← hI] at hb
  obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨c, ?_⟩
  have hsF : algebraMap (𝓞 F) F (s : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hs0
  have key : IsLocalization.mk' F b s - algebraMap (𝓞 F) F c = IsLocalization.mk' F r s := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← hyr, map_add, map_mul]
    field_simp
    ring
  rw [key, HeightOneSpectrum.valuation_of_mk', div_lt_one₀ (zero_lt_iff.mpr hvs)]
  have hr' := (HeightOneSpectrum.intValuation_le_pow_iff_mem p r (n + 1)).2 hr
  have hs' : ¬ p.intValuation (s : 𝓞 F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
    hn1 ((HeightOneSpectrum.intValuation_le_pow_iff_mem p _ _).1 h)
  exact lt_of_le_of_lt hr' (not_le.1 hs')

theorem card_res_le (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) ≤ Ideal.absNorm p.asIdeal := by
  have := L.lf
  have hint : ∀ a : 𝓞 F, (L.ιF.comp (algebraMap (𝓞 F) F)) a ∈ 𝒪[L.Fp] := fun a => by
    rw [Valuation.mem_integer_iff]
    exact (v_le_one_iff L _).2 (HeightOneSpectrum.valuation_le_one p a)
  let φ : 𝓞 F →+* 𝒪[L.Fp] := (L.ιF.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[L.Fp] hint
  let ρ : 𝓞 F →+* IsLocalRing.ResidueField 𝒪[L.Fp] := (IsLocalRing.residue 𝒪[L.Fp]).comp φ
  have hmax : ∀ z : 𝒪[L.Fp], valuation L.Fp (z : L.Fp) < 1 → z ∈ IsLocalRing.maximalIdeal 𝒪[L.Fp] :=
    fun z hz => (IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hz))
  have hker : ∀ a ∈ p.asIdeal, ρ a = 0 := by
    intro a ha
    show IsLocalRing.residue _ (φ a) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply hmax
    show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a)) < 1
    rw [v_lt_one_iff L]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem p a).2 ha
  have hsurj : Function.Surjective ρ := by
    intro w
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
    have hU : IsOpen {z : L.Fp | valuation L.Fp (z - (y : L.Fp)) < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro z0 hz0
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_setOf_eq, Units.val_one] at hz hz0 ⊢
      have : z0 + z - (y : L.Fp) = (z0 - y) + z := by ring
      rw [this]
      exact Valuation.map_add_lt _ hz0 hz
    obtain ⟨x, hx⟩ := L.dense.exists_mem_open hU ⟨(y : L.Fp), by simp⟩
    simp only [Set.mem_setOf_eq] at hx
    have hxI : valuation L.Fp (L.ιF x) ≤ 1 := by
      have : L.ιF x = (L.ιF x - y) + y := by ring
      rw [this]
      exact Valuation.map_add_le _ hx.le ((Valuation.mem_integer_iff _ _).1 y.2)
    obtain ⟨a, ha⟩ := exists_int_approx x ((v_le_one_iff L x).1 hxI)
    have ha' : valuation L.Fp (L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) < 1 := by
      rw [← map_sub]
      exact (v_lt_one_iff L _).2 ha
    refine ⟨a, ?_⟩
    show IsLocalRing.residue _ (φ a) = IsLocalRing.residue _ y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply hmax
    show valuation L.Fp (L.ιF (algebraMap (𝓞 F) F a) - y) < 1
    have : L.ιF (algebraMap (𝓞 F) F a) - (y : L.Fp) =
        -(L.ιF x - L.ιF (algebraMap (𝓞 F) F a)) + (L.ιF x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact ha') hx
  let ρq := Ideal.Quotient.lift p.asIdeal ρ hker
  have hsurjq : Function.Surjective ρq := by
    intro w
    obtain ⟨a, ha⟩ := hsurj w
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩
  haveI : Finite (𝓞 F ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  calc Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) ≤ Nat.card (𝓞 F ⧸ p.asIdeal) :=
        Nat.card_le_card_of_surjective ρq hsurjq
    _ = Ideal.absNorm p.asIdeal := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem one_lt_card_res (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    1 < Nat.card (IsLocalRing.ResidueField 𝒪[L.Fp]) := by
  have := L.lf
  exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance

end Res

theorem factor_bounds {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Real.exp (-(2 * |t|)) ≤ 1 - t ∧ 1 - t ≤ Real.exp (2 * |t|) := by
  have ha := abs_nonneg t
  constructor
  · have hpos : 0 < 1 - |t| := by linarith
    have hinv : (1 - |t|)⁻¹ ≤ 1 + 2 * |t| := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    have hlog : -(2 * |t|) ≤ Real.log (1 - |t|) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      linarith
    calc Real.exp (-(2 * |t|)) ≤ Real.exp (Real.log (1 - |t|)) := Real.exp_le_exp.2 hlog
      _ = 1 - |t| := Real.exp_log hpos
      _ ≤ 1 - t := by linarith [le_abs_self t]
  · have := Real.add_one_le_exp (2 * |t|)
    linarith [neg_abs_le t]

theorem prod_bounds (N : ℕ) (hN : 2 ≤ N) (η : ℝ) (hη : η = 1 ∨ η = -1) (a b k : ℕ) (hk : 1 ≤ k)
    (hak : k ≤ a) :
    Real.exp (-(4 * ((N : ℝ)⁻¹) ^ k)) ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ∧
      ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ≤ Real.exp (4 * ((N : ℝ)⁻¹) ^ k) := by
  set x : ℝ := (N : ℝ)⁻¹ with hx
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hx1 : x < 1 := by linarith
  have habs : ∀ i, |η ^ i / (N : ℝ) ^ i| = x ^ i := by
    intro i
    rcases hη with h | h <;> simp [h, abs_div, abs_pow, hx, inv_pow]
  have hsmall : ∀ i ∈ Finset.Icc a b, |η ^ i / (N : ℝ) ^ i| ≤ 1 / 2 := by
    intro i hi
    rw [habs]
    have hi1 : 1 ≤ i := le_trans hk (le_trans hak (Finset.mem_Icc.1 hi).1)
    calc x ^ i ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1.le hi1
      _ = x := pow_one x
      _ ≤ 1 / 2 := hx2
  have hsum : ∑ i ∈ Finset.Icc a b, 2 * x ^ i ≤ 4 * x ^ k := by
    rw [← Finset.mul_sum]
    have h1 : ∑ i ∈ Finset.Icc a b, x ^ i ≤ ∑ i ∈ Finset.Ico a (b + 1), x ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hi ⊢
        omega
      · intro i _ _
        positivity
    have h2 := geom_sum_Ico_le_of_lt_one (m := a) (n := b + 1) hx0 hx1
    have h3 : x ^ a / (1 - x) ≤ 2 * x ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg hx0 a]
    have h4 : x ^ a ≤ x ^ k := pow_le_pow_of_le_one hx0 hx1.le hak
    linarith
  have hlo : ∀ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) ≤ 1 - η ^ i / (N : ℝ) ^ i := by
    intro i hi
    have := (factor_bounds (hsmall i hi)).1
    rwa [habs] at this
  have hhi : ∀ i ∈ Finset.Icc a b, 1 - η ^ i / (N : ℝ) ^ i ≤ Real.exp (2 * x ^ i) := by
    intro i hi
    have := (factor_bounds (hsmall i hi)).2
    rwa [habs] at this
  constructor
  · calc Real.exp (-(4 * x ^ k)) ≤ Real.exp (-(∑ i ∈ Finset.Icc a b, 2 * x ^ i)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ∏ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) := by
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) :=
          Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hlo
  · calc ∏ i ∈ Finset.Icc a b, (1 - η ^ i / (N : ℝ) ^ i) ≤ ∏ i ∈ Finset.Icc a b, Real.exp (2 * x ^ i) :=
          Finset.prod_le_prod (fun i hi => le_trans (Real.exp_pos _).le (hlo i hi)) hhi
      _ = Real.exp (∑ i ∈ Finset.Icc a b, 2 * x ^ i) := by rw [Real.exp_sum]
      _ ≤ Real.exp (4 * x ^ k) := Real.exp_le_exp.2 hsum

open Formalism.L2.SG.DataInst Formalism.MainNotions.S.LocalSplitGroups

theorem etaP_pm {D : Formalism.BasicNotions.D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs <;> simp

theorem absNorm_two_le {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  omega

theorem aPD_bounds {D : Formalism.BasicNotions.D7} (p : PlF D) (T : ℕ) (hk : 1 ≤ D.R.k) :
    Real.exp (-(4 * ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ D.R.k)) ≤ aPD p T ∧
      aPD p T ≤ Real.exp (4 * ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ D.R.k) := by
  unfold aPD
  apply prod_bounds _ (absNorm_two_le p) _ (etaP_pm p) _ _ _ hk
  split_ifs <;> omega

theorem alpBoundU (D : Formalism.BasicNotions.D7) :
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → ∀ (u u' : D.what₂.Word) (p : PlF D),
      Real.exp (-(2 * (((Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)) ^
          (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤ alpD u u' p ∧
        alpD u u' p ≤ Real.exp (2 * (((Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)) ^
          (D.R.k - 2 * D.R.rS - 2))⁻¹) := by
  intro hk u u' p
  set m := D.R.k - 2 * D.R.rS - 2 with hm
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ) with hq
  have hN2 : 2 ≤ Ideal.absNorm p.asIdeal := absNorm_two_le p
  have hq1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast one_lt_card_res (D.s.atP p)
  have hqN : q ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by rw [hq]; exact_mod_cast card_res_le (D.s.atP p)
  set x : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ with hx
  have hk1 : 1 ≤ D.R.k := by omega
  have hkm : D.R.k = m + (2 * D.R.rS + 2) := by omega
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx, inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by exact_mod_cast hN2
    linarith
  have hkey : 8 * x ^ D.R.k ≤ 2 * (q ^ m)⁻¹ := by
    have h1 : x ^ D.R.k = x ^ m * x ^ (2 * D.R.rS + 2) := by rw [← pow_add, ← hkm]
    have h2 : x ^ (2 * D.R.rS + 2) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 (by linarith) (by omega)
    have h3 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have h4 : x ^ m ≤ (q ^ m)⁻¹ := by
      rw [hx, inv_pow]
      apply inv_anti₀ (pow_pos (by linarith) m)
      exact pow_le_pow_left₀ (by linarith) hqN m
    have h5 : 0 ≤ x ^ m := pow_nonneg hx0 m
    have h6 : x ^ m * x ^ (2 * D.R.rS + 2) ≤ x ^ m * (1 / 4) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) h5
    rw [h1]
    linarith
  have hA := aPD_bounds p (D.mem u).A.T hk1
  have hA' := aPD_bounds p (D.mem u').A.T hk1
  have hlow : Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := Real.exp_le_exp.2 (by linarith)
  have hup : Real.exp (8 * x ^ D.R.k) ≤ Real.exp (2 * (q ^ m)⁻¹) := Real.exp_le_exp.2 hkey
  have hxk : 0 ≤ x ^ D.R.k := pow_nonneg hx0 _
  unfold alpD
  split_ifs
  · constructor
    · calc Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := hlow
        _ ≤ Real.exp (-(4 * x ^ D.R.k)) := Real.exp_le_exp.2 (by linarith)
        _ ≤ aPD p (D.mem u).A.T := hA.1
    · calc aPD p (D.mem u).A.T ≤ Real.exp (4 * x ^ D.R.k) := hA.2
        _ ≤ Real.exp (8 * x ^ D.R.k) := Real.exp_le_exp.2 (by linarith)
        _ ≤ Real.exp (2 * (q ^ m)⁻¹) := hup
  · constructor
    · calc Real.exp (-(2 * (q ^ m)⁻¹)) ≤ Real.exp (-(8 * x ^ D.R.k)) := hlow
        _ = Real.exp (-(4 * x ^ D.R.k)) * Real.exp (-(4 * x ^ D.R.k)) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ aPD p (D.mem u).A.T * aPD p (D.mem u').A.T :=
            mul_le_mul hA.1 hA'.1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hA.1)
    · calc aPD p (D.mem u).A.T * aPD p (D.mem u').A.T ≤ Real.exp (4 * x ^ D.R.k) * Real.exp (4 * x ^ D.R.k) :=
            mul_le_mul hA.2 hA'.2 (le_trans (Real.exp_pos _).le hA'.1) (Real.exp_pos _).le
        _ = Real.exp (8 * x ^ D.R.k) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (2 * (q ^ m)⁻¹) := hup

end Formalism.L2.SG.IntegralApproximation
