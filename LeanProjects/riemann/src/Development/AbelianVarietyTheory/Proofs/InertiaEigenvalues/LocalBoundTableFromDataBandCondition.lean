import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NBand

theorem prime_eq_of_mem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    p = q := by
  by_contra hne
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h1) (w.asIdeal.mul_mem_left b h2)

theorem logb_le_of_le_four_exp {l : ℕ} (hl : (11 : ℝ) ≤ l) {large₂ h : ℝ} (hL : 1 ≤ large₂) (h0 : 0 ≤ h)
    (hh : h ≤ 4 * Real.exp large₂) : Real.logb l h ≤ large₂ := by
  have hl1 : (1 : ℝ) < l := by linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hloge : Real.log 4 + 1 ≤ Real.log l := by
    have he := Real.exp_one_lt_d9
    have : Real.log (4 * Real.exp 1) = Real.log 4 + 1 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
    rw [← this]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlpos : 0 < Real.log l := Real.log_pos hl1
  rcases h0.eq_or_lt with h0' | h0'
  · rw [← h0', Real.logb_zero]; linarith
  have h1 : Real.logb l h ≤ Real.logb l (4 * Real.exp large₂) := Real.logb_le_logb_of_le hl1 h0' hh
  refine h1.trans ?_
  rw [Real.logb, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, div_le_iff₀ hlpos]
  nlinarith

theorem band_arith {lr s z Wb Lb e S Sc eta₃ lg large₂ T CB C : ℝ} (hl : 11 ≤ lr) (hs0 : 0 ≤ s)
    (hzs : |z - s| ≤ T) (hb1 : Lb - T ≤ Wb) (hb2 : Wb ≤ Lb - T + 1) (he : e ≤ eta₃) (hS : S ≤ Sc)
    (hlg : lg ≤ large₂) (hLg : 1 ≤ large₂) (hSc : 0 ≤ Sc) (hLb : 0 ≤ Lb) (hT : 1 / 2 ≤ T) (hTe : 2 * T + 1 ≤ eta₃)
    (hCB : 0 ≤ CB) (hC : 6 * CB + 1 ≤ C)
    (habs : |lr * z - Wb| ≤ CB * (lr * e + lr * S + Wb / lr + z + lr * lg)) :
    |lr * s - Lb| ≤ C * (lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂) := by
  set E := lr * eta₃ + lr * Sc + Lb / lr + s + lr * large₂ with hE
  have hlr0 : 0 < lr := by linarith
  rw [abs_le] at hzs habs
  have hA : lr * e + lr * S + Wb / lr + z + lr * lg ≤ E + lr * eta₃ := by
    have e1 : lr * e ≤ lr * eta₃ := mul_le_mul_of_nonneg_left he hlr0.le
    have e2 : lr * S ≤ lr * Sc := mul_le_mul_of_nonneg_left hS hlr0.le
    have e3 : Wb / lr ≤ Lb / lr + 1 / lr := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hlr0.le
    have e3' : 1 / lr ≤ 1 := by rw [div_le_one hlr0]; linarith
    have e5 : lr * lg ≤ lr * large₂ := mul_le_mul_of_nonneg_left hlg hlr0.le
    have e6 : eta₃ ≤ lr * eta₃ := by nlinarith
    rw [hE]; linarith
  have hEge : lr * eta₃ ≤ E := by
    have : 0 ≤ Lb / lr := div_nonneg hLb hlr0.le
    have : 0 ≤ lr * Sc := mul_nonneg hlr0.le hSc
    have : 0 ≤ lr * large₂ := mul_nonneg hlr0.le (by linarith)
    rw [hE]; linarith
  have hEt0 : 0 ≤ lr * eta₃ := mul_nonneg hlr0.le (by linarith)
  have hx1 : lr * T + T ≤ lr * eta₃ := by nlinarith
  have hCBA : CB * (lr * e + lr * S + Wb / lr + z + lr * lg) ≤ CB * (E + lr * eta₃) :=
    mul_le_mul_of_nonneg_left hA hCB
  have hCE : (2 * CB + 1) * E ≤ C * E := mul_le_mul_of_nonneg_right (by linarith) (hEt0.trans hEge)
  have hm1 : lr * (s - z) ≤ lr * T := mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hm2 : -(lr * T) ≤ lr * (s - z) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by linarith) hlr0.le
  have hCBE : CB * (lr * eta₃) ≤ CB * E := mul_le_mul_of_nonneg_left hEge hCB
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.NBand

theorem GlobalTheory.NBand.bandPlaceWeightApproximation_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C := by
  intro D L P HW X R C hX hR hpar
  intro i lam hTw hb l hl hlp
  obtain ⟨h11, π, hπ, hw, Cx, hG, Wd, hBase, hBox, hNT, hBand⟩ := (hX.band i lam).1 hb
  have hli : l = D.nd.l i := prime_eq_of_mem hlp (D.nd.lPrime i).out hl hw
  subst hli
  obtain ⟨a, hnt, -, habs⟩ := hBand
  obtain ⟨s, hs1, hs2, hs3⟩ := hBox.nt a hnt
  refine ⟨s, hs1, hs2, ?_⟩
  obtain ⟨-, hCB, -, -, -, -, -, -, -, hC6, -⟩ := hR
  have hl11 : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hLg : 1 ≤ TwistedPlaces.large₂ L := by
    unfold TwistedPlaces.large₂ Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hbexp : L.sc.b = Real.exp (TwistedPlaces.large₂ L) := rfl
  have hpar' : L.Sc + L.etaSz + (D.R.t : ℝ) + 2 ≤ L.sc.b := hpar
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hetaP : TwistedPlaces.eta₃ L = L.etaSz + D.R.t + 2 := rfl
  have hhB : TwistedPlaces.hB L = L.sc.b + L.Sc + L.etaSz + D.R.t + 2 := rfl
  have hh17n : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz ≤ Wd.b + Wd.η + Wd.S := by
    have := hNT.w20
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; split_ifs <;> omega
  have hh17 : ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ) ≤ (Wd.b : ℝ) + Wd.η + Wd.S := by
    exact_mod_cast hh17n
  have hhle := hBase.h_le
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ)) ≤ TwistedPlaces.large₂ L := by
    apply logb_le_of_le_four_exp hl11 hLg (by positivity)
    rw [← hbexp]; linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b
    apply div_nonneg
    · exact div_nonneg (mul_nonneg hx.le (Real.exp_pos _).le) (Real.exp_pos _).le
    · exact mul_nonneg hx.le (Nat.cast_nonneg _)
  exact band_arith hl11 (hw0.trans hs1) hs3 hBox.b_lo hBox.b_hi hBase.η_le hBase.S_le hlg hLg hSc.le
    (by rw [hbexp]; exact (Real.exp_pos _).le) (by linarith) (by rw [hetaP]; linarith) hCB hC6 habs
