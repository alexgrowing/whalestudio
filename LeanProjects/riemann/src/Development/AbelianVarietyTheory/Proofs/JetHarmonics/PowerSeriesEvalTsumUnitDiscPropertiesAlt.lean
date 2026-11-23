import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscPropertiesStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem powerSeriesEvalTsum_unitDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  intro K _ _ _ x hx
  have A := GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, B9, lowerOffDiagonalCoeff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨C1, C2, C3, C4, C5, C6, C7, C8⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K Unit (fun _ => x) (fun _ => hx)
  have hev : ∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t) := A.2.1
  have P1 : ∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x) := by
    intro f hf
    rw [A.2.2.1, hev]
    exact C1 f hf
  have P2 : ∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧
      ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x := by
    intro f g hf hg
    simp only [hev]
    exact C2 f g hf hg
  have P3 : ∀ a : K, ev1 (PowerSeries.C a) x = a := by
    intro a
    rw [hev]
    exact C3 a
  have P4 : ev1 PowerSeries.X x = x := by
    rw [hev]
    exact C4 ()
  have hBddX : Bdd (PowerSeries.X : PowerSeries K) := (B3 _ 0).2.2 (B5 ()).1
  have hBddP : ∀ P : Polynomial K, Bdd (P : PowerSeries K) := by
    intro P
    rw [(lowerOffDiagonalCoeff _).2]
    refine ⟨∑ i ∈ P.support, ‖P.coeff i‖, fun m => ?_⟩
    rw [Polynomial.coeff_coe]
    by_cases hm : m ∈ P.support
    · exact Finset.single_le_sum (f := fun i => ‖P.coeff i‖) (fun i _ => norm_nonneg _) hm
    · have h0 : P.coeff m = 0 := by simpa using hm
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have P5 : ∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x := by
    intro P
    refine ⟨hBddP P, ?_⟩
    refine Polynomial.induction_on P ?_ ?_ ?_
    · intro a
      rw [Polynomial.coe_C, P3, Polynomial.eval_C]
    · intro p q hp hq
      rw [Polynomial.coe_add, (P2 _ _ (hBddP p) (hBddP q)).1, hp, hq, Polynomial.eval_add]
    · intro m a ih
      have e : (Polynomial.C a * Polynomial.X ^ (m + 1) : Polynomial K) =
          (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [e, Polynomial.coe_mul, Polynomial.coe_X, (P2 _ _ (hBddP _) hBddX).2.2, ih, P4]
      simp
  have P6 : ∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) →
      ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x := by
    intro ι t f hf
    classical
    induction t using Finset.induction_on with
    | empty =>
      have h1 : (1 : PowerSeries K) = PowerSeries.C 1 := by simp
      rw [Finset.prod_empty, Finset.prod_empty, h1, P3]
    | @insert j s hj ih =>
      have hs : ∀ i ∈ s, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        (P2 _ _ (hf j (Finset.mem_insert_self j s)) ((B6 ι s f).2 hs).1).2.2, ih hs]
  have P7 : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧
      ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧
      ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2 := by
    have hI : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 := fun f hf => by
      rw [hev]
      exact (C5 f hf).1
    have hsh : ∀ f : PowerSeries K, Intg f →
        Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) ∧
        ev1 f x = PowerSeries.coeff 0 f +
          x * ev1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) x := by
      intro f hf
      have hg : Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) := by
        rw [(lowerOffDiagonalCoeff _).1]
        intro m
        rw [PowerSeries.coeff_mk]
        exact (lowerOffDiagonalCoeff f).1.mp hf (m + 1)
      refine ⟨hg, ?_⟩
      have hgb := (B3 _ 0).2.2 hg
      have e : ev1 f x = ev1 ((PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) +
          PowerSeries.C (PowerSeries.constantCoeff f)) x :=
        congrArg (fun F => ev1 F x) (PowerSeries.eq_X_mul_shift_add_const f)
      rw [e, (P2 _ _ (B2 _ _ hBddX hgb).2.2
        (show Bdd (PowerSeries.C (PowerSeries.constantCoeff f)) from (B4 _).1)).1, (P2 _ _ hBddX hgb).2.2, P4, P3,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      ring
    intro f hf
    obtain ⟨hg, e1⟩ := hsh f hf
    obtain ⟨hh, e2⟩ := hsh _ hg
    rw [PowerSeries.coeff_mk, zero_add] at e2
    refine ⟨hI f hf, ?_, ?_⟩
    · rw [e1, add_sub_cancel_left, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hI _ hg)
    · have key : ∀ a b d : K, a + x * (b + x * d) - a - b * x = x ^ 2 * d := by
        intro a b d
        ring
      rw [e1, e2, key, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hI _ hh)
  have P8 : ∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f →
      ev1 (f.subst g) x = ev1 f (ev1 g x) := by
    intro f g hg h0 hf
    rw [hev (f.subst g), hev g]
    exact C8 g f hg h0 hf
  have P9 : ∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h →
      PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 →
      ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x =
        ev F ![ev1 g x, ev1 h x] := by
    intro F g h hF hg hh hg0 hh0
    rw [hev, C7 (Fin 2) ![g, h] F (fun j => by fin_cases j; exacts [hg, hh])
      (fun j => by fin_cases j; exacts [hg0, hh0]) hF]
    congr 1
    funext j
    fin_cases j <;> simp [hev]
  have product_first_zeroth_parts : ∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F →
      Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y] := by
    intro F y hy hF
    have hs : ∀ i, Small ((![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i) := by
      intro i
      fin_cases i
      · exact B5 ()
      · exact (B4 y).2.2 hy
    have hFb : Bdd F := ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 F 0).2.2 hF
    have D := GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K (Fin 2) Unit _ F hs hFb
    rw [A.2.2.2.2.1 F y]
    refine ⟨D.2.2.1 hF, ?_⟩
    rw [hev, C6 (Fin 2) _ F hs hFb]
    congr 1
    funext j
    fin_cases j
    · exact C4 ()
    · exact C3 y
  have product_first_partition : ∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f := by
    intro f
    unfold ev1
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp
  exact ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, product_first_zeroth_parts, product_first_partition⟩

end GlobalTheory.ConvSer
