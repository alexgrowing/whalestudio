import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEltPrescribedValuationsBalancedArchimedeanStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CovHtCmp

section Scalars

variable {K : Type} [Field K] [NumberField K]

theorem vLa_mul_of_ne (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vLa la (x * y) = vLa la x + vLa la y := by
  have h1 : la.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : la.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  simp only [vLa, map_mul, WithZero.log_mul h1 h2]
  ring

theorem vLa_natCast_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

theorem le_vLa_of_pow_dvd (la : HeightOneSpectrum (𝓞 K)) {p n N : ℕ} (hN : N ≠ 0) (h : p ^ n ∣ N) :
    n * vLa la (p : K) ≤ vLa la (N : K) := by
  obtain ⟨m, rfl⟩ := h
  have h1 := mul_ne_zero_iff.1 hN
  have h2 : vLa la (((p ^ n : ℕ)) : K) = n * vLa la (p : K) := by
    simp [vLa, WithZero.log_pow]
  rw [Nat.cast_mul, vLa_mul_of_ne la (Nat.cast_ne_zero.2 h1.1) (Nat.cast_ne_zero.2 h1.2), h2]
  linarith [vLa_natCast_nonneg la h1.2]

theorem exists_scalar (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℝ)
    (ha : ∀ p ∈ S, 0 ≤ a p) : ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧ (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧
      (∀ la, ∀ p ∈ S, (τ : ℝ) * (e la + vLa la (p : K) * a p) ≤ (vLa la α : ℝ)) ∧
      ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ + ∑ p ∈ S, a p * Real.log p) + C := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_elt_prescribed_valuations_balanced_archimedean K e t ht
  refine ⟨C + ∑ p ∈ S, Real.log p, fun τ => ?_⟩
  obtain ⟨α, h0, h1, h2⟩ := hC τ
  set N : ℕ := ∏ p ∈ S, p ^ ⌈τ * a p⌉₊ with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  refine ⟨N * α, mul_ne_zero hNK h0, fun la => ?_, fun la p hp => ?_, fun σ => ?_⟩
  · have h3 : (0 : ℝ) ≤ vLa la (N : K) := by exact_mod_cast vLa_natCast_nonneg la hN0
    rw [vLa_mul_of_ne la hNK h0, Int.cast_add]
    linarith [h1 la]
  · have h3 : (⌈τ * a p⌉₊ : ℝ) * vLa la (p : K) ≤ vLa la (N : K) := by
      exact_mod_cast le_vLa_of_pow_dvd la hN0 (Finset.dvd_prod_of_mem (fun p => p ^ ⌈τ * a p⌉₊) hp)
    have h4 : (0 : ℝ) ≤ vLa la (p : K) := by exact_mod_cast vLa_natCast_nonneg la (hS p hp).ne_zero
    have h5 := mul_le_mul_of_nonneg_right (Nat.le_ceil (τ * a p)) h4
    rw [vLa_mul_of_ne la hNK h0, Int.cast_add]
    nlinarith [h1 la]
  · have h3 : Real.log N ≤ τ * ∑ p ∈ S, a p * Real.log p + ∑ p ∈ S, Real.log p := by
      rw [hN, Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast pow_ne_zero _ (hS p hp).ne_zero),
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p hp => ?_
      rw [Nat.cast_pow, Real.log_pow]
      have h4 := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg (α := ℝ) τ) (ha p hp))).le
      nlinarith [Real.log_natCast_nonneg p]
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast,
      Real.log_mul (Nat.cast_ne_zero.2 hN0) (norm_ne_zero_iff.2 ((map_ne_zero σ).2 h0))]
    nlinarith [h2 σ]

variable {R : Type} [CommRing R] [Algebra K R] {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal}

theorem le_val_pow_mul (hv : IsVal la v) {θ f : R} {a b : ℝ} (ha : (a : EReal) ≤ v θ) (hb : (b : EReal) ≤ v f) (k : ℕ) :
    ((k * a + b : ℝ) : EReal) ≤ v (θ ^ k * f) := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    rw [pow_succ', mul_assoc, hv.mul, show ((k + 1 : ℕ) : ℝ) * a + b = a + (k * a + b) by push_cast; ring, EReal.coe_add]
    exact add_le_add ha ih

end Scalars

theorem countVol_mono_eventually (D d a : ℕ) {m m' : ℕ → ℕ∞} (h : ∀ᶠ k in Filter.atTop, m (a * k) ≤ m' (a * k)) :
    countVol D d a m ≤ countVol D d a m' :=
  Filter.limsup_le_limsup (h.mono fun _ hk => ENNReal.div_le_div_right (mul_le_mul_right
    (EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 hk))) _) _)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem weightAbsEntrySum_nsmul (τ : ℕ) (u : AllWt.Weight Dw) : CovHt.l1 (τ • u) = τ * CovHt.l1 u := by
  simp [CovHt.l1, Finset.mul_sum, abs_mul]

theorem weightAbsEntrySum_nonneg (u : AllWt.Weight Dw) : 0 ≤ CovHt.l1 u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [IsCMField E] in

theorem htEx_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ htEx E p := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have : (0 : ℝ) ≤ p - 1 := by linarith
  unfold htEx
  positivity

omit [NumberField E] [IsCMField E] in

theorem even_nsmul_snd {G : WTZ E} (hG : Even G.2) (k : ℕ) : Even (k • G).2 := by
  rw [Prod.smul_snd, nsmul_eq_mul]
  exact hG.mul_left _

theorem homN_pow_mul_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2)
    (θ f : Rul Xo c) {z : Σ k, Frame (U.X k).Ψ r} (hz : z.2 ∈ (U.X z.1).dom) (k : ℕ) :
    homN U x (k • G + G') (θ ^ k * f) z = homN U x G θ z ^ k * homN U x G' f z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : Even (k • G + G').2 := (even_nsmul_snd hG k).add hG'
    rw [succ_nsmul', add_assoc, pow_succ', mul_assoc, homN_mul U x hG he _ _ _ hz, ih]
    ring

theorem wt_split (u u' : AllWt.Weight Dw) (k : ℕ) :
    (8 * k) • wtOf Dw u 0 = k • wtOf Dw ((8 : ℤ) • (u - u')) 0 + (8 * k) • wtOf Dw u' 0 := by
  simp only [nsmul_wtOf, ← wtOf_add, smul_zero, add_zero]
  congr 1
  module

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem eq_zero_of_genVal {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) :
    f = 0 := by
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  refine secZ_eq_zero_of_genVal (cuspW_le_secZ G hf.1) fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · rw [genVal_apply h, evC_eq_zero h hZ hf.2]

theorem le_val_of_mixVals (hc : HTCmp Xo c) {B : ℝ} {Z : Comp Xo c} {u : AllWt.Weight Dw} {τ : ℕ}
    {f : cuspOn U Z (τ • wtOf Dw u 0)} (hf : f ∈ latVal U (mixVals Xo c B) Z (τ • wtOf Dw u 0))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) :
    0 ≤ v f ∨ ∃ p ∈ htPrimes l B,
      ((-(τ * (vLa la (p : c.F) * (htEx E p * CovHt.l1 u))) : ℝ) : EReal) ≤ v f := by
  by_cases h : ∃ p ∈ htPrimes l B, ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal
  · obtain ⟨p, hp, hla⟩ := h
    obtain ⟨w, hw, hle⟩ := hc p la hp.1 hla v hv
    have hs : (f : Rul Xo c) ∈ secZ Xo c (exOf Dw (τ • u) 0) := by
      have e : wtOf Dw (τ • u) 0 = τ • wtOf Dw u 0 := by rw [nsmul_wtOf, smul_zero]
      rw [exOf, e]
      exact cuspW_le_secZ _ f.2.1
    have h0 : 0 ≤ w f := hf la w (by rw [mixVals_of_mem hp hla]; exact hw)
    have h1 := h0.trans (hle _ _ hs)
    refine Or.inr ⟨p, hp, ?_⟩
    rw [weightAbsEntrySum_nsmul] at h1
    induction hx : v f using EReal.rec with
    | bot => rw [hx] at h1; simp at h1
    | top => exact le_top
    | coe b =>
      rw [hx, ← EReal.coe_add, EReal.coe_nonneg] at h1
      rw [EReal.coe_le_coe_iff]
      nlinarith
  · exact Or.inl (hf la v (by
      have : (mixVals Xo c B).1 la = (recVals Xo c).1 la := if_neg h
      rw [this]; exact hv))

theorem fin_bound {Z : Comp Xo c} {G G' : WTZ E} {θ : Rul Xo c} {e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (hN : NoBase U Z G) (hF : FinBd U Z G 8 θ e) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G')
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {k : ℕ} {α : c.F}
    (hα : α ≠ 0) {b : ℝ} (hb : ((-b : ℝ) : EReal) ≤ v f) (ha : ((8 * k : ℕ) : ℝ) * e la + b ≤ vLa la α) :
    ((8 * k : ℕ) : EReal) * depthOn U Z G v ≤ v (α • (θ ^ k * f)) := by
  have hV := (recVals Xo c).2 la v hv
  by_cases ht : v f = ⊤
  · rw [hV.smul _ _ hα, hV.mul, ht, EReal.add_top_of_ne_bot (hV.ne_bot _),
      EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  obtain ⟨w, hw, hwt⟩ := hN la v hv G' f hf ht
  have h1 := hF la v hv ⟨w, hw, hwt⟩
  have h2 : 0 ≤ depthOn U Z G v := le_iInf₂ fun w hw => hw la v hv
  have h3 : depthOn U Z G v ≤ v w := iInf₂_le w hw
  obtain ⟨d, hd⟩ : ∃ d : ℝ, depthOn U Z G v = d :=
    ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top hwt h3) (ne_bot_of_le_ne_bot EReal.zero_ne_bot h2)).symm⟩
  rw [hd] at h1 ⊢
  have h4 : ((8 * d - 8 * e la : ℝ) : EReal) ≤ v θ := by
    induction hx : v θ using EReal.rec with
    | bot => exact absurd hx (hV.ne_bot _)
    | top => exact le_top
    | coe a =>
      rw [hx, ← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
      rw [EReal.coe_le_coe_iff]
      push_cast at h1
      linarith
  rw [hV.smul _ _ hα]
  refine le_trans ?_ (add_le_add le_rfl (le_val_pow_mul hV h4 hb k))
  rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have : (vAdd la α : ℝ) = vLa la α := rfl
  push_cast at ha ⊢
  nlinarith

theorem inf_bound {a b n s t T : ℝ} {B : ℝ≥0∞} {k : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n)
    (h1 : ENNReal.ofReal a ^ 2 ≤ ENNReal.ofReal (Real.exp (2 * (8 : ℕ) * s)) * B ^ 8)
    (h2 : b ≤ Real.exp ((8 * k : ℕ) * t)) (h3 : Real.log n ≤ (8 * k : ℕ) * (T - t - s)) :
    ENNReal.ofReal (n * (a ^ k * b)) ^ 2 ≤ ENNReal.ofReal (Real.exp (2 * (8 * k : ℕ) * T)) * B ^ (8 * k) := by
  have h4 : n * b ≤ Real.exp ((8 * k : ℕ) * (T - s)) := by
    have := mul_le_mul ((Real.log_le_iff_le_exp hn).1 h3) h2 hb (Real.exp_pos _).le
    rw [← Real.exp_add] at this
    exact this.trans_eq (by congr 1; ring)
  calc ENNReal.ofReal (n * (a ^ k * b)) ^ 2 = ENNReal.ofReal (n * b) ^ 2 * (ENNReal.ofReal a ^ 2) ^ k := by
        rw [show n * (a ^ k * b) = n * b * a ^ k by ring, ENNReal.ofReal_mul (mul_nonneg hn.le hb),
          ENNReal.ofReal_pow ha]
        ring
    _ ≤ ENNReal.ofReal (Real.exp ((8 * k : ℕ) * (T - s))) ^ 2 *
          (ENNReal.ofReal (Real.exp (2 * (8 : ℕ) * s)) * B ^ 8) ^ k := by gcongr
    _ = _ := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul,
          ← Real.exp_nat_mul, ← Real.exp_add]
        congr 3
        push_cast
        ring

variable (U) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

theorem compVol_le_volL (hc : HTCmp Xo c) (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc B t ε : ℝ)
    (hM : Mult U x V dict Z u u' cc) (hε : 0 < ε) :
    compVol U x 8 (mixVals Xo c B) Z (wtOf Dw u' 0) t ≤
      volL U x V dict 8 Z (wtOf Dw u 0) (t + cc + htCost l B * CovHt.l1 u' + ε) := by
  obtain ⟨hN, θ, e, s, ⟨-, hθ, hcar⟩, hF, ⟨hs, hI⟩, hcc⟩ := hM
  have hfin := htPrimes_finite (l := l) B
  obtain ⟨C, hC⟩ := exists_scalar e s hs hfin.toFinset (fun p hp => (hfin.mem_toFinset.1 hp).1)
    (fun p => htEx E p * CovHt.l1 u') fun p hp => mul_nonneg (htEx_nonneg (hfin.mem_toFinset.1 hp).1) (weightAbsEntrySum_nonneg u')
  have hsum : ∑ p ∈ hfin.toFinset, htEx E p * CovHt.l1 u' * Real.log p = htCost l B * CovHt.l1 u' := by
    rw [htCost, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  refine countVol_mono_eventually _ _ _ ((Filter.eventually_ge_atTop ⌈|C| / ε⌉₊).mono fun k hk => ?_)
  have hk' : C ≤ ((8 * k : ℕ) : ℝ) * ε := by
    have h1 := (div_le_iff₀ hε).1 (Nat.ceil_le.1 hk)
    have h2 : (0 : ℝ) ≤ k * ε := by positivity
    push_cast
    linarith [le_abs_self C]
  obtain ⟨α, hα, h1, h2, h3⟩ := hC (8 * k)
  refine Set.encard_le_encard_of_injOn
    (f := fun f => ⟨α • (θ ^ k * f), Submodule.smul_mem _ _ (hcar k f f.2)⟩) (fun f hf => ⟨fun la v hv => ?_, ?_⟩) ?_
  · rcases le_val_of_mixVals hc hf.1 hv with h | ⟨p, hp, h⟩
    · exact fin_bound hN hF f.2 hv hα (b := 0) (by simpa using h) (by simpa using h1 la)
    · exact fin_bound hN hF f.2 hv hα h ((mul_add _ _ _).symm.trans_le (h2 la p (hfin.mem_toFinset.2 hp)))
  · intro σ hσ y hy
    show ENNReal.ofReal (homN (U σ) x _ (α • (θ ^ k * (f : Rul Xo c))) _) ^ 2 ≤ _
    have he : Even ((8 * k) • wtOf Dw u' 0).2 := even_nsmul_snd (even_wtOf u' 0) _
    rw [FlatLine.homN_smul, wt_split u u', homN_pow_mul_eq (U σ) x (even_wtOf _ 0) he θ f y.2.2]
    refine inf_bound (homN_nonneg _ _ _ _ _) (homN_nonneg _ _ _ _ _) (norm_pos_iff.2 ((map_ne_zero σ).2 hα))
      (hI σ hσ y hy) (hf.2 σ hσ _ hy) ((h3 σ).trans ?_)
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left hcc (Nat.cast_nonneg (α := ℝ) (8 * k))]
  · intro f _ g _ h
    have h4 := congrArg (genVal Z) (congrArg Subtype.val h)
    simp only [map_smul, map_mul, map_pow] at h4
    have h5 := mul_left_cancel₀ (pow_ne_zero k hθ) (smul_right_injective _ hα h4)
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_genVal (sub_mem f.2 g.2) (by rw [map_sub, h5, sub_self])))

end Generic

theorem compVol_le_volL_deep : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → HTCmp Y.d.Xo₂ Y.d.c₂ → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u u' : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (cc B t ε : ℝ), Mult Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z u u' cc → 0 < ε → compVol Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) Z (wtOf (T.Q.Dw j) u' 0) t ≤ volL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict 8 Z (wtOf (T.Q.Dw j) u 0) (t + cc + htCost Y.d.l₂ B * GlobalTheory.CovHt.l1 u' + ε) :=
  fun _ _ _ Y _ _ _ _ hc Z u u' cc B t ε hM hε => compVol_le_volL Y.U _ _ Y.dict hc Z u u' cc B t ε hM hε

end GlobalTheory.CovHtCmp
