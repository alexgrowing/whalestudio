import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslateStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThShift

variable {q : ℕ} [Fact q.Prime]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (F : ℂ → ℂ)
    (hF : AnalyticAt ℂ F 0) (m : ℕ) : hat ι ℓ (fun z => F z ^ m) = hat ι ℓ F ^ m := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ
  induction m with
  | zero => simpa using h2 1
  | succ k ih =>
    have hk : AnalyticAt ℂ (fun z => F z ^ k) 0 := hF.pow k
    have := (h1 _ F hk hF).2.1
    simp only [pow_succ]
    rw [this, ih]

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
  simp [this]

theorem hat_funEq (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (F G : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (α : ℂ) (a : ℤ_[q]) (ha : ι α = zc a) (m : ℕ)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z) = F z ^ m * G z) :
    (hat ι (C ω * logS) F).subst (mulS a : ℂ_[q]⟦X⟧)
      = hat ι (C ω * logS) F ^ m * hat ι (C ω * logS) G := by
  obtain ⟨h1, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q ι _ (const_ell ω)
  rw [← (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω F hF).2.2.1 α a ha,
    ← hat_pow ι _ (const_ell ω) F hF m]
  have hk : AnalyticAt ℂ (fun z => F z ^ m) 0 := hF.pow m
  rw [← (h1 _ G hk hG).2.1]
  have hα : AnalyticAt ℂ (fun z => F (α * z)) 0 := by
    have h0 : AnalyticAt ℂ (fun z : ℂ => α * z) 0 := by fun_prop
    exact AnalyticAt.comp_of_eq hF h0 (by simp)
  exact (h1 _ _ hα (hk.mul hG)).2.2.1 h

theorem bd_pow (f : ℂ_[q]⟦X⟧) (hf : Bd 1 f) (m : ℕ) : Bd 1 (f ^ m) := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2
    simpa [pow_succ] using this

theorem shift_pow (ζ : ℂ_[q]) (hζ : ‖ζ - 1‖ < 1) (f : ℂ_[q]⟦X⟧) (hf : Bd 1 f) (m : ℕ) :
    shiftS ζ (f ^ m) = shiftS ζ f ^ m := by
  obtain ⟨-, h2, h3, -⟩ := GlobalTheory.MomOne.Shift.shift_laws q ζ hζ
  induction m with
  | zero => simpa using h3 1
  | succ k ih =>
    rw [pow_succ, (h2 _ _ ⟨1, bd_pow f hf k⟩ ⟨1, hf⟩).2, ih, pow_succ]

theorem not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso; first | exact hs.ne' h | omega | (simp at h; omega)
  subst hv
  have : (2 * u : ℝ) = -1 := by simp at hre; linarith
  have : 2 * u = -1 := by exact_mod_cast this
  omega

theorem zc_natCast (k : ℕ) : zc (k : ℤ_[q]) = (k : ℂ_[q]) := by simp [zc]

theorem zc_sub_one (a : ℤ_[q]) : zc (a - 1) = zc a - 1 := by simp [zc]

theorem coprime_pred (m : ℕ) (hm : 1 ≤ m) (h : ‖(m : ℂ_[q])‖ < 1) : Nat.Coprime (m - 1) q := by
  have hn := (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.2.2
  rw [← zc_natCast, hn] at h
  have h1 : (q : ℤ) ∣ (m : ℤ) := by
    rw [← PadicInt.norm_int_lt_one_iff_dvd]; simpa using h
  have h2 : q ∣ m := by exact_mod_cast h1
  rw [Nat.coprime_comm, (Fact.out : q.Prime).coprime_iff_not_dvd]
  intro h3
  have h4 : q ∣ m - (m - 1) := Nat.dvd_sub h2 h3
  have h5 : m - (m - 1) = 1 := by omega
  rw [h5] at h4
  exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h4)

theorem W_mul_eq (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (θ : ℂ → ℂ) (hd : d.Prime) (hd7 : d % 16 = 7)
    (hs : Split d q) (hθ : IsTh d θ) (n : ℕ) (y : ℂ) (hy : Good ι d n 1 y) (α : ℂ) (hα : InOK d α)
    (hα1 : ‖ι α - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ))) : W1 d (α * y) θ = W1 d y θ := by
  obtain ⟨⟨o1, -, oR⟩, oZ, oD, -⟩ := GlobalTheory.MomOne.okArith d q ι hd hd7 hs
  have hn := (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.2.2
  have hle : ∀ β, InOK d β → ‖ι β‖ ≤ 1 := by
    intro β hβ
    obtain ⟨a, ha⟩ := (oZ β hβ).1
    rw [ha, hn]; exact a.norm_le_one
  have hmul : ∀ a b, InOK d a → InOK d b → InOK d (a * b) := fun a b ha hb => (oR a b ha hb).2.1
  have hconj : ∀ a, InOK d a → InOK d (conj a) := fun a ha => (oR a a ha ha).2.2.2
  obtain ⟨v, hv, hvn, rfl⟩ := hy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hβ : InOK d (α - 1) := by
    have := (oR α (-1) hα (oR 1 1 o1 o1).2.2.1).1
    simpa [sub_eq_add_neg] using this
  have hl : InOK d ((α - 1) * v / (q : ℂ) ^ n) := by
    apply oD _ n (hmul _ _ hβ hv)
    · rw [map_mul, norm_mul, map_sub, map_one]
      calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * 1 :=
            mul_le_mul hα1 (hle v hv) (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    · rw [map_mul, map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-(2 * n : ℤ)) :=
            mul_le_mul (hle _ (hconj _ hβ)) hvn (norm_nonneg _) (by positivity)
        _ ≤ _ := by
            rw [one_mul]; exact zpow_le_zpow_right₀ hq1 (by omega)
  have hc : InOK d (conj v * (v * conj (α - 1)) / (q : ℂ) ^ (2 * n)) := by
    apply oD _ (2 * n) (hmul _ _ (hconj _ hv) (hmul _ _ hv (hconj _ hβ)))
    · rw [map_mul, norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
            mul_le_mul hvn (hle _ (hmul _ _ hv (hconj _ hβ))) (norm_nonneg _) (by positivity)
        _ = _ := by push_cast; ring
    · have : conj (conj v * (v * conj (α - 1))) = conj v * (v * (α - 1)) := by
        simp only [map_mul, Complex.conj_conj]; ring
      rw [this, map_mul, norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
            mul_le_mul hvn (hle _ (hmul _ _ hv hβ)) (norm_nonneg _) (by positivity)
        _ = _ := by push_cast; ring
  have hW := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.2.2.2.1 (((1 : ℕ) : ℂ) * v / (q : ℂ) ^ n)
    ((α - 1) * v / (q : ℂ) ^ n) θ (by omega) (by
      convert hc using 1
      simp only [map_div₀, map_mul, map_pow, Complex.conj_natCast]
      field_simp
      push_cast
      ring)
  rw [hθ.2.2.2.1 _ hl] at hW
  rw [hW]
  congr 1
  push_cast
  ring

theorem theta_shift : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → hat M.ι (C ω * logS) (W1 d y θ) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) θ) := by
  intro d q _ M ω θ hd hd7 hs hL hM hθ hAt n y hy
  obtain ⟨hζq, hA⟩ := hAt n y hy
  set ζ := M.ι (kap1 d 1 y) with hζdef
  have hζ : ‖ζ - 1‖ < 1 := hA.2.1
  obtain ⟨⟨o1, -, oR⟩, oZ, oD, oE, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hs
  obtain ⟨mu1, -, -, -, -, hn⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨-, sh2, sh3, -⟩ := GlobalTheory.MomOne.Shift.shift_laws q ζ hζ
  obtain ⟨-, -, -, ht0, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ (const_ell ω)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hθy : θ y ≠ 0 := by
    intro h0
    have h1 := hθ.2.2.2.2 y h0
    have := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hs hL hM).2.2.2 y 1 0 o1 one_ne_zero
      ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (by simpa using h1) hA.1
    exact not_half d hd.pos this.2
  have hθan : AnalyticAt ℂ θ 0 := hθ.1.analyticAt 0
  have hWan : AnalyticAt ℂ (W1 d y θ) 0 :=
    ((GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.2.1 y θ hθ.1).2.analyticAt 0
  set f := hat M.ι (C ω * logS) θ with hf
  set g := hat M.ι (C ω * logS) (W1 d y θ) with hg
  have hfb : Bd 1 f := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd7 hs hL hM hθ
  have hf0 : constantCoeff f = 1 := by rw [hf, ht0, hθ.2.1, map_one]
  have hff : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (by rw [hf0]; exact one_ne_zero)
  have hfi : Bd 1 f⁻¹ := (GlobalTheory.MomOne.sup_norm_laws q).2.2.1 f _ hfb (by rw [hf0, norm_one]) hff
  set h := shiftS ζ f with hh
  set h' := shiftS ζ f⁻¹ with hh'
  have hhh : h * h' = 1 := by
    rw [hh, hh', ← (sh2 _ _ ⟨1, hfb⟩ ⟨1, hfi⟩).2, hff]
    simpa using sh3 1
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : constantCoeff g = 0 := by rw [h0, map_zero]
    rw [hg, ht0, _root_.map_eq_zero] at h1
    simp [W1, U1, hθy] at h1
  have hρ : g * h' ≠ 0 := mul_ne_zero hg0 (right_ne_zero_of_mul_eq_one hhh)
  have key : ∀ s : ℕ, Nat.Coprime s q → ∃ m : ℕ, 2 ≤ m ∧ ‖(m : ℂ_[q])‖ < 1 ∧ s ∣ m ∧
      ∃ c : ℂ_[q], g * h' = C c ∧ c ^ (m - 1) = 1 := by
    intro s hsq
    obtain ⟨e, he, he1, he2⟩ := oE (n + 1) s hsq
    have hsO : InOK d (s : ℂ) := ⟨s, 0, by simp⟩
    set α := (s : ℂ) * e with hαdef
    have hα : InOK d α := (oR _ _ hsO he).2.1
    obtain ⟨⟨a, ha⟩, -, -⟩ := oZ α hα
    obtain ⟨-, ⟨N, hN⟩, -⟩ := oZ e he
    obtain ⟨⟨b, hb⟩, -, -⟩ := oZ _ hsO
    have hlt : (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) < 1 := zpow_lt_one_of_neg₀ hq1 (by omega)
    have hlen : (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) :=
      zpow_le_zpow_right₀ hq1.le (by omega)
    have hα1 : ‖M.ι α‖ = 1 := by
      have h1 : ‖M.ι α - 1‖ < ‖(1 : ℂ_[q])‖ := by rw [norm_one]; exact lt_of_le_of_lt he1 hlt
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
      rw [sub_add_cancel, max_eq_right h1.le, norm_one] at this
      exact this
    have hα0 : α ≠ 0 := by
      intro h0; rw [h0] at hα1; simp at hα1
    have hm : ((s * s * N : ℕ) : ℂ) = α * conj α := by
      push_cast
      rw [hN, hαdef, map_mul, Complex.conj_natCast]; ring
    set m := s * s * N with hmdef
    have hmn : ‖(m : ℂ_[q])‖ < 1 := by
      have h1 : (m : ℂ_[q]) = M.ι α * (M.ι s * M.ι (conj e)) := by
        rw [← map_natCast M.ι m, hm, ← map_mul, ← map_mul, hαdef, map_mul (starRingEnd ℂ),
          Complex.conj_natCast]
      rw [h1, norm_mul, hα1, one_mul, norm_mul, hb, hn]
      calc _ ≤ 1 * (q : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) :=
            mul_le_mul b.norm_le_one he2 (norm_nonneg _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hlt
    have hm2 : 2 ≤ m := by
      have h0 : m ≠ 0 := by
        intro h0
        rw [h0] at hm
        simp [hα0] at hm
      have h1 : m ≠ 1 := by
        intro h1
        rw [h1] at hmn
        simp at hmn
      omega
    refine ⟨m, hm2, hmn, ⟨s * N, by rw [hmdef]; ring⟩, ?_⟩
    obtain ⟨ε, hε1, hε2, -, hε4, hε5, hε6⟩ :=
      GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd hd7 hs hL hM hθ α m hα hα0 hm
    obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ y ε hM hA hε1 hε2 ⟨1, hε4⟩
    have hWW := W_mul_eq d M.ι θ hd hd7 hs hθ n y hy α hα (he1.trans hlen)
    have e1 : f.subst (mulS a : ℂ_[q]⟦X⟧) = f ^ m * hat M.ι (C ω * logS) ε := by
      apply hat_funEq M.ι ω θ ε hθan hε2 α a ha m
      have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
        hθan.continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun z hz => hε5 z hz
    have e2 : g.subst (mulS a : ℂ_[q]⟦X⟧) = g ^ m * hat M.ι (C ω * logS) ψ := by
      apply hat_funEq M.ι ω _ ψ hWan hψ1 α a ha m
      have hc : ContinuousAt (fun z => θ (z + y)) 0 :=
        (hθ.1.continuous.comp (continuous_id.add continuous_const)).continuousAt
      have : ∀ᶠ z in 𝓝 (0 : ℂ), θ (z + y) ≠ 0 := hc.eventually_ne (by simpa using hθy)
      filter_upwards [this.filter_mono nhdsWithin_le_nhds, hψ2] with z hz hz2
      rw [hz2, ← hε6 y z hz, hWW]
    have ha1 : ‖a - ((1 : ℕ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
      rw [Nat.cast_one, ← hn, zc_sub_one, ← ha]; exact he1.trans hlen
    have e3 : h.subst (mulS a : ℂ_[q]⟦X⟧) = h ^ m * hat M.ι (C ω * logS) ψ := by
      have := ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n 1 a f hζq ha1 ⟨1, hfb⟩).2
      rw [pow_one, e1, (sh2 _ _ ⟨1, bd_pow f hfb m⟩ ⟨1, hε4⟩).2, shift_pow ζ hζ f hfb m] at this
      rw [hψ3, this]
    have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' (mu1 a).2.1
    have e4 : h.subst (mulS a : ℂ_[q]⟦X⟧) * h'.subst (mulS a : ℂ_[q]⟦X⟧) = 1 := by
      rw [← subst_mul hsub, hhh, ← coe_substAlgHom hsub, map_one]
    have e5 : (g * h').subst (mulS a : ℂ_[q]⟦X⟧) = (g * h') ^ m := by
      rw [subst_mul hsub, e2]
      rw [e3] at e4
      have e6 : h ^ m * h' ^ m = 1 := by rw [← mul_pow, hhh, one_pow]
      rw [mul_pow]
      linear_combination (g ^ m * h' ^ m) * e4
        - (g ^ m * hat M.ι (C ω * logS) ψ * h'.subst (mulS a : ℂ_[q]⟦X⟧)) * e6
    exact (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m (mu1 a).2.1
      (by rw [(mu1 a).2.2.1, ← ha, hα1]) hmn hm2).1 _ hρ e5
  obtain ⟨m₁, h12, h1n, -, c, hc, hc1⟩ := key 1 (Nat.coprime_one_left q)
  obtain ⟨m₂, h22, -, ⟨k, hk⟩, c', hc', hc2⟩ := key (m₁ - 1) (coprime_pred m₁ (by omega) h1n)
  have hcc : c' = c := C_injective (hc'.symm.trans hc)
  rw [hcc] at hc2
  have hone : c = 1 := by
    have h1 : c ^ m₂ = 1 := by rw [hk, pow_mul, hc1, one_pow]
    have h2 : m₂ = (m₂ - 1) + 1 := by omega
    rw [h2, pow_succ, hc2, one_mul] at h1
    exact h1
  rw [hone, map_one] at hc
  linear_combination h * hc - g * hhh

end GlobalTheory.MomOne.ThShift
