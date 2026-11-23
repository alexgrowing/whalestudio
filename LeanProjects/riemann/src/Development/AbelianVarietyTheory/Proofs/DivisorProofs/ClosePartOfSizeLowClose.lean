import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.ShFam

namespace GlobalTheory.RegEst.Close

theorem sum_coef_mul_le {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ) (hu : Dom u) (f : ι → Fin N → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (h₀ : ∀ τ (i : Fin N), ¬ (i : ℕ) + 1 < N → f τ i = 0)
    (hf : ∀ τ (i : Fin N), (i : ℕ) + 1 < N → f τ i ≤ B) :
    ∑ τ, ∑ i, coef u τ i * f τ i ≤ 2 * ((Fintype.card ι : ℝ) * N) * ‖u‖ * B := by
  have hab : ∀ τ i, |u τ i| ≤ ‖u‖ := fun τ i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)
  have hn : 0 ≤ ‖u‖ := norm_nonneg _
  have term : ∀ τ (i : Fin N), coef u τ i * f τ i ≤ 2 * ‖u‖ * B := fun τ i => by
    by_cases hi : (i : ℕ) + 1 < N
    · have h1 : 0 ≤ coef u τ i := coef_nonneg (fun τ a b hab => hu τ a b hab) τ hi
      have h2 : coef u τ i ≤ 2 * ‖u‖ := by
        rw [coef, dif_pos hi]
        have := hab τ i
        have := hab τ ⟨i + 1, hi⟩
        have := le_abs_self (u τ i)
        have := neg_abs_le (u τ ⟨i + 1, hi⟩)
        linarith
      calc coef u τ i * f τ i ≤ coef u τ i * B := mul_le_mul_of_nonneg_left (hf τ i hi) h1
        _ ≤ 2 * ‖u‖ * B := mul_le_mul_of_nonneg_right h2 hB
    · rw [h₀ τ i hi, mul_zero]
      positivity
  calc ∑ τ, ∑ i, coef u τ i * f τ i ≤ ∑ _τ : ι, ∑ _i : Fin N, 2 * ‖u‖ * B :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => term τ i
    _ = 2 * ((Fintype.card ι : ℝ) * N) * ‖u‖ * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem log_le_div_mul {l r : ℝ} (hl : Real.exp 1 ≤ l) (hr : l ≤ r) : Real.log r ≤ Real.log l / l * r := by
  have hr0 : 0 < r := (Real.exp_pos 1).trans_le (hl.trans hr)
  have h := Real.log_div_self_antitoneOn (show l ∈ {x : ℝ | Real.exp 1 ≤ x} from hl)
    (show r ∈ {x : ℝ | Real.exp 1 ≤ x} from hl.trans hr) hr
  calc Real.log r = Real.log r / r * r := by field_simp
    _ ≤ Real.log l / l * r := mul_le_mul_of_nonneg_right h hr0.le

end GlobalTheory.RegEst.Close

namespace GlobalTheory.RegEst

open Close in

theorem closePart_of_steps : SizeSt → LowSt → CloseSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.ClosePart (T.F c) := by
  intro hS hL hC D O hO hN A T H h c
  obtain ⟨x, P, hc⟩ := hO
  have hex : ∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H) := ⟨A, T, H, ⟨h⟩⟩
  obtain ⟨C₁, hC₁, hS⟩ := hS D O x P hc hN hex
  obtain ⟨C₂, t₂, hC₂, ht₂, hL⟩ := hL D O x P hc hN hex
  obtain ⟨t₃, ht₃, hC⟩ := hC D O x P hc hN hex
  have hA := h.an c
  set K : ℝ := (Fintype.card D.what₂.Tau : ℝ) * O.N with hK
  have hK0 : 0 ≤ K := by positivity
  set L₀ : ℝ := max 3 (max (-Real.log t₂) (-Real.log t₃)) with hL₀
  have hL₀3 : 3 ≤ L₀ := le_max_left _ _
  have hL₀2 : -Real.log t₂ ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀3' : -Real.log t₃ ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hL₀pos : 0 < L₀ := by linarith
  refine ⟨(Real.sqrt L₀)⁻¹, by positivity, K * (1 + C₁ + C₂), fun C hC0 u hu s hs hss l hl a => ?_⟩
  have hlL : L₀ ≤ l := by
    have h1 : s ^ 2 ≤ L₀⁻¹ := by
      calc s ^ 2 ≤ ((Real.sqrt L₀)⁻¹) ^ 2 := pow_le_pow_left₀ hs.le hss 2
        _ = L₀⁻¹ := by rw [inv_pow, Real.sq_sqrt hL₀pos.le]
    have h2 := inv_anti₀ (by positivity) h1
    rwa [inv_inv, ← hl] at h2
  have hl3 : 3 ≤ l := hL₀3.trans hlL
  have hle : Real.exp 1 ≤ l := by have := Real.exp_one_lt_d9; linarith
  set t := Real.exp (-l) with ht
  have htpos : 0 < t := Real.exp_pos _
  have ht2 : t ≤ t₂ := by
    rw [ht, ← Real.exp_log ht₂]
    exact Real.exp_le_exp.2 (by linarith)
  have ht3 : t ≤ t₃ := by
    rw [ht, ← Real.exp_log ht₃]
    exact Real.exp_le_exp.2 (by linarith)
  have hlog : Real.log (1 / t) = l := by rw [ht, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hcube : t ^ ((1 : ℝ) / 3) = Real.exp (-l / 3) := by
    rw [ht, ← Real.exp_mul]
    ring_nf
  have hts : Real.exp (-(s ^ 2)⁻¹) = t := by rw [ht, hl]
  have hKC : K ≤ C := by nlinarith [mul_nonneg hK0 (add_nonneg hC₁ hC₂)]
  have hKC2 : K * (C₁ + C₂) ≤ C := by nlinarith
  have hC0' : 0 ≤ C := hK0.trans hKC
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  have hq0 : 0 ≤ Real.log l / l := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hex0 : 0 ≤ Real.exp (-l / 3) := (Real.exp_pos _).le
  intro z hz
  have hy : (h.man c).pt a z ∈ offBd O.Φ c ((h.man c).ε a) := fun hb => hz ((hA.Z a z).2 hb)
  have hr : (T.M c).r a z = O.met.r c ((h.man c).ε a) ((h.man c).pt a z) := hA.r a z hz
  have hr1 : 1 ≤ Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)) := by
    have := Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)
    have h2 := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at h2

  have key : (T.F c).phS u s a z - (T.F c).ph u a z = (∑ τ, ∑ i, coef u τ i *
      (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
        phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) / 2 := by
    rw [hA.phS u s hs a z, hA.ph u a z hz, hts, hc.reg_eq]
    have e := hc.two_mul_chg c u ((h.man c).ε a) ((h.man c).pt a z)
    have e2 : P.reg c ((h.man c).ε a) u t ((h.man c).pt a z) -
        phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z) = ∑ τ, ∑ i, coef u τ i *
          (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
            phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z)) := by
      have e3 := phW_eq_sum (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z)
      unfold PolDat.reg
      erw [e3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
    linarith
  have h₀ : ∀ τ (i : Fin O.N), ¬ (i : ℕ) + 1 < O.N → P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
      phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z) = 0 := fun τ i hi => by
    simp [PolDat.regFund, hi, extBd, hy]

  have near : (T.M c).r a z ≤ l → (T.F c).phS u s a z - (T.F c).ph u a z ≤ K * ‖u‖ * Real.exp (-l / 3) := by
    intro hrl
    have hsum : (∑ τ, ∑ i, coef u τ i *
        (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
          phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * Real.exp (-l / 3) := sum_coef_mul_le u hu _ hex0 h₀ fun τ i hi => by
      have := hC t htpos ht3 c ((h.man c).ε a) τ i hi _ hy (by rw [← hr, hlog]; exact hrl)
      rw [hcube] at this
      linarith
    rw [key]
    linarith

  have far : (T.F c).phS u s a z - (T.F c).ph u a z ≤
      K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))) := by
    have hB : 0 ≤ (C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)) :=
      mul_nonneg (add_nonneg hC₁ hC₂) (by linarith)
    have hsum : (∑ τ, ∑ i, coef u τ i *
        (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
          phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))) := sum_coef_mul_le u hu _ hB h₀ fun τ i hi => by
      obtain ⟨-, hup, -⟩ := hL t htpos ht2 c ((h.man c).ε a) τ i hi ((h.man c).pt a z)
      obtain ⟨hlo, -⟩ := hS c ((h.man c).ε a) τ i _ hy
      nlinarith [mul_le_mul_of_nonneg_left hr1 hC₂]
    rw [key]
    linarith
  refine ⟨fun hrl => ?_, ?_⟩
  · have := near hrl
    have h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0
    have h2 : 0 ≤ C * ‖u‖ * (Real.log l / l) := mul_nonneg (mul_nonneg hC0' hn) hq0
    linarith
  · have h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0
    have hr0 : 0 ≤ (T.M c).r a z := by rw [hr]; linarith [Real.exp_pos 1, Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)]
    have h2 : 0 ≤ C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := mul_nonneg (mul_nonneg (mul_nonneg hC0' hn) hq0) hr0
    rcases le_or_gt ((T.M c).r a z) l with hrl | hrl
    · have := near hrl
      linarith
    · have := far
      have h3 := log_le_div_mul hle (hr ▸ hrl.le)
      rw [← hr] at h3 this
      have h4 : K * ‖u‖ * ((C₁ + C₂) * Real.log ((T.M c).r a z)) ≤
          C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := by
        have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg hK0 hn) (add_nonneg hC₁ hC₂))
        have h6 := mul_le_mul_of_nonneg_right hKC2 (mul_nonneg (mul_nonneg hn hq0) hr0)
        calc K * ‖u‖ * ((C₁ + C₂) * Real.log ((T.M c).r a z))
            = K * ‖u‖ * (C₁ + C₂) * Real.log ((T.M c).r a z) := by ring
          _ ≤ K * ‖u‖ * (C₁ + C₂) * (Real.log l / l * (T.M c).r a z) := h5
          _ = K * (C₁ + C₂) * (‖u‖ * (Real.log l / l) * (T.M c).r a z) := by ring
          _ ≤ C * (‖u‖ * (Real.log l / l) * (T.M c).r a z) := h6
          _ = C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := by ring
      have h7 : 0 ≤ C * ‖u‖ * Real.exp (-l / 3) := mul_nonneg (mul_nonneg hC0' hn) hex0
      linarith

end GlobalTheory.RegEst
