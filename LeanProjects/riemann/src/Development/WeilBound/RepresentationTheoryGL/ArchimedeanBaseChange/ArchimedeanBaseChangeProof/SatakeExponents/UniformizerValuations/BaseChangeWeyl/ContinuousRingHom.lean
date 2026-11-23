import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf

noncomputable section

open NumberField IsDedekindDomain Polynomial Topology WithZero

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

namespace ConjugationUpperEntries

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

instance compat : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _

theorem isEquiv : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv Valued.v :=
  ValuativeRel.isEquiv _ _

theorem exists_nat_lt_one : ∃ d : ℕ, 0 < d ∧ Valued.v ((d : w.adicCompletion E)) < 1 := by
  refine ⟨Ideal.absNorm w.asIdeal, Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w
    ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w
    ((Ideal.absNorm w.asIdeal : ℕ) : E)
  simp only [map_natCast] at h1 h2
  rw [← map_natCast (algebraMap E (w.adicCompletion E))]
  exact (h2.trans_lt h1 : _)

theorem exists_root {d : ℕ} (hd : Valued.v ((d : w.adicCompletion E)) < 1) (t : ℕ) (x : w.adicCompletion E)
    (hx : Valued.v x ≤ 1) : ∃ y : w.adicCompletion E, y ^ (d * t + 1) = 1 + d * x ^ (d * t + 1) := by
  let O := Valuation.integer (ValuativeRel.valuation (w.adicCompletion E))
  have hxO : x ∈ O := by
    change ValuativeRel.valuation _ x ≤ 1
    exact ((isEquiv w).le_one_iff_le_one).mpr hx
  let xo : O := ⟨x, hxO⟩
  have hdO : (d : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : Valued.v (b : w.adicCompletion E) ≤ 1 := ((isEquiv w).le_one_iff_le_one).mp b.2
    have h1 : Valued.v (((d : O) * b : O) : w.adicCompletion E) = 1 := by rw [hb]; simp
    have h2 : Valued.v (((d : O) * b : O) : w.adicCompletion E) < 1 := by
      have : (((d : O) * b : O) : w.adicCompletion E) = (d : w.adicCompletion E) * b := by push_cast; rfl
      rw [this, map_mul]
      calc Valued.v (d : w.adicCompletion E) * Valued.v (b : w.adicCompletion E)
          ≤ Valued.v (d : w.adicCompletion E) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hd
    exact (ne_of_lt h2) h1
  let f : O[X] := X ^ (d * t + 1) - C (1 + (d : O) * xo ^ (d * t + 1))
  have hmon : f.Monic := monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  have hf1 : f.eval 1 ∈ IsLocalRing.maximalIdeal O := by
    have : f.eval 1 = -(xo ^ (d * t + 1)) * d := by
      simp only [f, eval_sub, eval_pow, eval_X, one_pow, eval_C]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hdO
  have hf2 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (f.derivative.eval 1)) := by
    have : f.derivative.eval 1 = (d : O) * t + 1 := by
      simp only [f, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
        eval_X, one_pow, mul_one]
      push_cast; ring
    rw [this, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ hdO), zero_add]
    exact isUnit_one
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O) f hmon 1 hf1 hf2
  refine ⟨(a : w.adicCompletion E), ?_⟩
  have ha' : a ^ (d * t + 1) = 1 + (d : O) * xo ^ (d * t + 1) := by
    have := ha
    simp only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.mp this
  have := congrArg (fun z : O => (z : w.adicCompletion E)) ha'
  simpa using this

theorem no_root {d m : ℕ} (a : ℤ) (hda : Valued.v ((d : w.adicCompletion E)) = exp a) (ha : a < 0) (hm : -a < m)
    (x : w.adicCompletion E) (hx : 1 < Valued.v x) : ¬ ∃ y : w.adicCompletion E, y ^ m = 1 + d * x ^ m := by
  have hx0 : Valued.v x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  set k := log (Valued.v x)
  have hvx : Valued.v x = exp k := (exp_log hx0).symm
  have hk : 0 < k := by
    have : exp (0 : ℤ) < exp k := by rw [exp_zero, ← hvx]; exact hx
    exact exp_lt_exp.mp this
  have hbig : Valued.v ((d : w.adicCompletion E) * x ^ m) = exp (a + m * k) := by
    rw [map_mul, map_pow, hda, hvx, ← exp_nsmul, ← exp_add, nsmul_eq_mul]
  have hpos : 0 < a + m * k := by nlinarith
  have hsum : Valued.v (1 + (d : w.adicCompletion E) * x ^ m) = exp (a + m * k) := by
    rw [Valuation.map_add_eq_of_lt_right, hbig]
    rw [hbig, map_one, ← exp_zero]
    exact exp_lt_exp.mpr hpos
  rintro ⟨y, hy⟩
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    have : Valued.v (y ^ m) = 0 := by rw [map_pow, h0, zero_pow]; omega
    rw [hy, hsum] at this
    exact exp_ne_zero this
  set j := log (Valued.v y)
  have hvy : Valued.v y = exp j := (exp_log hy0).symm
  have h1 : exp ((m : ℤ) * j) = exp (a + m * k) := by
    rw [← hsum, ← hy, map_pow, hvy, ← exp_nsmul, nsmul_eq_mul]
  have h2 : (m : ℤ) * j = a + m * k := exp_injective h1
  have h3 : (m : ℤ) * (j - k) = a := by linarith
  rcases le_or_gt 0 (j - k) with h | h
  · nlinarith
  · nlinarith

theorem le_one_of_le_one (s : w.adicCompletion E →+* w.adicCompletion E) {d : ℕ} (hd0 : 0 < d)
    (hd : Valued.v ((d : w.adicCompletion E)) < 1) (x : w.adicCompletion E) (hx : Valued.v x ≤ 1) :
    Valued.v (s x) ≤ 1 := by
  have hne : Valued.v ((d : w.adicCompletion E)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (w.adicCompletion E))]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0.ne')
  set a := log (Valued.v ((d : w.adicCompletion E)))
  have hda : Valued.v ((d : w.adicCompletion E)) = exp a := (exp_log hne).symm
  have ha : a < 0 := by
    have : exp a < exp (0 : ℤ) := by rw [exp_zero, ← hda]; exact hd
    exact exp_lt_exp.mp this
  have hm : -a < ((d * a.natAbs + 1 : ℕ) : ℤ) := by
    have h0 : ((d * a.natAbs + 1 : ℕ) : ℤ) = (d : ℤ) * (a.natAbs : ℤ) + 1 := by push_cast; ring
    have h1 : (1 : ℤ) ≤ d := by exact_mod_cast hd0
    have h2 : (0 : ℤ) ≤ a.natAbs := by positivity
    have h3 : -a ≤ (a.natAbs : ℤ) := by omega
    have h4 : (1 : ℤ) * (a.natAbs : ℤ) ≤ (d : ℤ) * (a.natAbs : ℤ) := mul_le_mul_of_nonneg_right h1 h2
    rw [h0]; linarith
  by_contra h
  push Not at h
  apply no_root w a hda ha hm (s x) h
  obtain ⟨y, hy⟩ := exists_root w hd a.natAbs x hx
  refine ⟨s y, ?_⟩
  rw [← map_pow, hy]
  simp

theorem continuous_ringHom (s : w.adicCompletion E →+* w.adicCompletion E) : Continuous s := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_lt_one w
  have hne : Valued.v ((d : w.adicCompletion E)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (w.adicCompletion E))]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0.ne')
  have hdK : (d : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mp hne
  set a := log (Valued.v ((d : w.adicCompletion E)))
  have hda : Valued.v ((d : w.adicCompletion E)) = exp a := (exp_log hne).symm
  have ha : a < 0 := by
    have : exp a < exp (0 : ℤ) := by rw [exp_zero, ← hda]; exact hd
    exact exp_lt_exp.mp this
  refine continuous_of_continuousAt_zero s ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' _)).mpr ?_
  intro γ hγ
  obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hr : Valued.v r ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (Valuation.ne_zero_iff _).mp hγ
  set b := log (Valued.v r)
  have hvr : Valued.v r = exp b := (exp_log hr).symm
  set n := b.natAbs + 1
  have hn : (n : ℤ) * a < b := by
    have h1 : (n : ℤ) = (b.natAbs : ℤ) + 1 := by simp only [n]; push_cast; ring
    have h2 : -b ≤ (b.natAbs : ℤ) := by omega
    have h3 : (n : ℤ) * (a + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    linarith
  refine ⟨ValuativeRel.valuation _ ((d : w.adicCompletion E) ^ n), ?_, ?_⟩
  · rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hdK
  intro x hx
  change ValuativeRel.valuation _ x < ValuativeRel.valuation _ _ at hx
  rw [(isEquiv w).lt_iff_lt] at hx
  change ValuativeRel.valuation _ (s x) < ValuativeRel.valuation _ r
  rw [(isEquiv w).lt_iff_lt]
  have hdn : (d : w.adicCompletion E) ^ n ≠ 0 := pow_ne_zero _ hdK
  have hz : Valued.v (x / (d : w.adicCompletion E) ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ (by rw [Valuation.pos_iff]; exact hdn)).mpr hx.le
  have hsz := le_one_of_le_one w s hd0 hd _ hz
  have hx' : x = (d : w.adicCompletion E) ^ n * (x / (d : w.adicCompletion E) ^ n) := by
    field_simp
  rw [hx', map_mul, map_pow, map_natCast, map_mul, map_pow, hda, hvr]
  calc exp a ^ n * Valued.v (s (x / (d : w.adicCompletion E) ^ n)) ≤ exp a ^ n * 1 := by gcongr
    _ = exp ((n : ℤ) * a) := by rw [mul_one, ← exp_nsmul, nsmul_eq_mul]
    _ < exp b := exp_lt_exp.mpr hn

end ConjugationUpperEntries

theorem cjEq : CjEq := by
  intro E _ _ _ w _ s hs
  have hc := ConjugationUpperEntries.continuous_ringHom w s
  have h : ∃ s' : w.adicCompletion E →+* w.adicCompletion E, Continuous s' ∧
      ∀ x : E, s' (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨s, hc, hs⟩
  have hcj : GlobalTheory.BCT.cj w = h.choose := by
    unfold GlobalTheory.BCT.cj
    rw [dif_pos h]
  rw [hcj]
  have hdense : DenseRange (algebraMap E (w.adicCompletion E)) := by
    apply HeightOneSpectrum.denseRange_algebraMap
  have := hdense.equalizer hc h.choose_spec.1 (funext fun x => by
    simp only [Function.comp_apply]
    rw [hs x, h.choose_spec.2 x])
  exact RingHom.ext fun x => congrFun this x

end PositivityTheory.Rg.BcB.F.LemB

end
