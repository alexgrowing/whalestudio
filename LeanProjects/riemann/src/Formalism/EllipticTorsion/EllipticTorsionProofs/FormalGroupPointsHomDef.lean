import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupPointsHom

open Formalism.ELL Formalism.G

section Analysis

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem summable_of_bound {ι : Type*} {f : ι → K} (deg : ι → ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (hfin : ∀ N : ℕ, {i | f i ≠ 0 ∧ deg i < N}.Finite)
    (h : ∀ i, ‖f i‖ ≤ r ^ deg i) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  refine Filter.eventually_cofinite.2 ((hfin N).subset ?_)
  intro i hi
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hi ⊢
  refine ⟨fun h0 => by rw [h0, norm_zero] at hi; linarith, ?_⟩
  by_contra hge
  push Not at hge
  have h1 := h i
  have h2 : r ^ deg i ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hge
  linarith

theorem degree_fin_two_eq_add_of_ne (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem finite_degree_lt (N : ℕ) : {d : Fin 2 →₀ ℕ | d.degree < N}.Finite := by
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun _ => N)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq, degree_fin_two_eq_add_of_ne] at hd
  simp only [Set.mem_Iic, Finsupp.le_def]
  intro i; fin_cases i <;> simp <;> omega

theorem norm_mono_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (d : Fin 2 →₀ ℕ) :
    ‖a ^ (d 0) * b ^ (d 1)‖ ≤ r ^ d.degree := by
  rw [degree_fin_two_eq_add_of_ne, pow_add, norm_mul, norm_pow, norm_pow]
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _) (pow_le_pow_left₀ (norm_nonneg _) hb _)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg hr _)

def term (F : MvPowerSeries (Fin 2) K) (a b : K) (d : Fin 2 →₀ ℕ) : K :=
  MvPowerSeries.coeff d F * (a ^ (d 0) * b ^ (d 1))

theorem evalMv2_eq (F : MvPowerSeries (Fin 2) K) (a b : K) :
    evalMv2 F a b = ∑' d, term F a b d := by
  unfold evalMv2 term; congr 1; funext d; ring

theorem norm_term_le {F : MvPowerSeries (Fin 2) K} (hF : IntegralMv F) {a b : K} {r : ℝ}
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (d : Fin 2 →₀ ℕ) : ‖term F a b d‖ ≤ r ^ d.degree := by
  unfold term
  rw [norm_mul]
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  calc ‖MvPowerSeries.coeff d F‖ * ‖a ^ (d 0) * b ^ (d 1)‖ ≤ 1 * r ^ d.degree :=
        mul_le_mul (hF d) (norm_mono_le ha hb d) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem summable_term {F : MvPowerSeries (Fin 2) K} (hF : IntegralMv F) {a b : K}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : Summable (term F a b) :=
  summable_of_bound Finsupp.degree (le_trans (norm_nonneg a) (le_max_left _ _))
    (max_lt ha hb) (fun N => (finite_degree_lt N).subset fun d hd => hd.2)
    (norm_term_le hF (le_max_left _ _) (le_max_right _ _))

def IL (K : Type u) [NormedField K] [IsUltrametricDist K] : Subring (MvPowerSeries (Fin 2) K) where
  carrier := {F | IntegralMv F}
  mul_mem' hF hG := SubstitutionCoefficientCongruence.integral_mul hF hG
  one_mem' := SubstitutionCoefficientCongruence.integral_one
  add_mem' {F G} hF hG := fun d => by
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))
  zero_mem' := fun d => by simp
  neg_mem' {F} hF := fun d => by rw [map_neg, norm_neg]; exact hF d

theorem mem_IL {F : MvPowerSeries (Fin 2) K} : F ∈ IL K ↔ IntegralMv F := Iff.rfl

theorem summable_prod_term {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => term F a b x.1 * term G a b x.2 := by
  have hr0 : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
  refine summable_of_bound (fun x => x.1.degree + x.2.degree) hr0 (max_lt ha hb) ?_ ?_
  · intro N
    refine ((finite_degree_lt N).prod (finite_degree_lt N)).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_prod, Set.mem_ofPred_eq]
    omega
  · intro x
    rw [norm_mul, pow_add]
    exact mul_le_mul (norm_term_le hF (le_max_left _ _) (le_max_right _ _) _)
      (norm_term_le hG (le_max_left _ _) (le_max_right _ _) _) (norm_nonneg _)
      (pow_nonneg hr0 _)

theorem evalMv2_one (a b : K) : evalMv2 (1 : MvPowerSeries (Fin 2) K) a b = 1 := by
  classical
  rw [evalMv2_eq, tsum_eq_single 0]
  · simp [term]
  · intro d hd
    simp [term, MvPowerSeries.coeff_one, hd]

theorem evalMv2_mul {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (F * G) a b = evalMv2 F a b * evalMv2 G a b := by
  classical
  rw [evalMv2_eq, evalMv2_eq, evalMv2_eq,
    (summable_term hF ha hb).tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_term hG ha hb)
      (summable_prod_term hF hG ha hb)]
  congr 1; funext n
  unfold term
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl]
  simp only [Finsupp.add_apply, pow_add]
  ring

theorem evalMv2_add {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (F + G) a b = evalMv2 F a b + evalMv2 G a b := by
  rw [evalMv2_eq, evalMv2_eq, evalMv2_eq,
    ← (summable_term hF ha hb).tsum_add (summable_term hG ha hb)]
  congr 1; funext d
  simp [term, add_mul]

def ev (a b : K) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : IL K →+* K where
  toFun F := evalMv2 F.1 a b
  map_one' := evalMv2_one a b
  map_mul' F G := evalMv2_mul F.2 G.2 ha hb
  map_zero' := by simp [evalMv2]
  map_add' F G := evalMv2_add F.2 G.2 ha hb

theorem ev_apply {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (F : IL K) :
    ev a b ha hb F = evalMv2 F.1 a b := rfl

theorem evalMv2_C (c a b : K) : evalMv2 (MvPowerSeries.C c : MvPowerSeries (Fin 2) K) a b = c := by
  classical
  rw [evalMv2_eq, tsum_eq_single 0]
  · simp [term]
  · intro d hd
    simp [term, MvPowerSeries.coeff_C, hd]

theorem evalMv2_X0 (a b : K) : evalMv2 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) a b = a := by
  classical
  rw [evalMv2_eq, tsum_eq_single (Finsupp.single 0 1)]
  · simp [term]
  · intro d hd
    simp [term, MvPowerSeries.coeff_X, hd]

theorem evalMv2_X1 (a b : K) : evalMv2 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) a b = b := by
  classical
  rw [evalMv2_eq, tsum_eq_single (Finsupp.single 1 1)]
  · simp [term]
  · intro d hd
    simp [term, MvPowerSeries.coeff_X, hd]

theorem evalMv2_subst_X0 (w : PowerSeries K) (a b : K) :
    evalMv2 (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) a b = evalPS w a := by
  classical
  rw [evalMv2_eq, evalPS]
  have hsupp : Function.support (term (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) a b)
      ⊆ Set.range (Finsupp.single (0 : Fin 2)) := by
    intro e he
    have := WeierstrassChordSeries.coeff_Wi w 0 e
    unfold WeierstrassChordSeries.Wi at this
    by_cases h : e = Finsupp.single 0 (e 0)
    · exact ⟨e 0, h.symm⟩
    · exfalso; apply he; simp [term, this, h]
  rw [← (Finsupp.single_injective (0 : Fin 2)).tsum_eq hsupp]
  congr 1; funext n
  have := WeierstrassChordSeries.coeff_Wi w 0 (Finsupp.single 0 n)
  unfold WeierstrassChordSeries.Wi at this
  simp [term, this]

theorem integral_of_mem {F : MvPowerSeries (Fin 2) K} (h : F ∈ IL K) : IntegralMv F := h

theorem coeff_subst_two (G s t : MvPowerSeries (Fin 2) K) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (G.subst ![s, t]) =
      ∑ᶠ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d G * MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1)) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs0, ht0])
  rw [MvPowerSeries.coeff_subst hst]
  congr 1; funext d
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  rfl

theorem coeff_mono_eq_zero {s t : MvPowerSeries (Fin 2) K} (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) {d e : Fin 2 →₀ ℕ} (h : e.degree < d.degree) :
    MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1)) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_mul)
  refine lt_of_lt_of_le ?_ (add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hs0)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ht0))
  rw [degree_fin_two_eq_add_of_ne d] at h
  exact_mod_cast h

theorem evalMv2_subst {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (G.subst ![s, t]) a b = evalMv2 G (evalMv2 s a b) (evalMv2 t a b) := by
  set M : (Fin 2 →₀ ℕ) → MvPowerSeries (Fin 2) K := fun d => s ^ (d 0) * t ^ (d 1) with hMdef
  have hM : ∀ d, IntegralMv (M d) := fun d =>
    SubstitutionCoefficientCongruence.integral_mul (SubstitutionCoefficientCongruence.integral_pow hs _) (SubstitutionCoefficientCongruence.integral_pow ht _)
  have hMev : ∀ d, evalMv2 (M d) a b = evalMv2 s a b ^ (d 0) * evalMv2 t a b ^ (d 1) := by
    intro d
    have h := map_mul (ev a b ha hb) ((⟨s, hs⟩ : IL K) ^ (d 0)) ((⟨t, ht⟩ : IL K) ^ (d 1))
    rw [map_pow, map_pow] at h
    simpa [ev_apply, hMdef] using h
  set T : (Fin 2 →₀ ℕ) → (Fin 2 →₀ ℕ) → K := fun d e =>
    MvPowerSeries.coeff d G * (MvPowerSeries.coeff e (M d) * (a ^ (e 0) * b ^ (e 1))) with hT
  have hr0 : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
  have hsum : Summable (Function.uncurry T) := by
    refine summable_of_bound (fun x => x.2.degree) hr0 (max_lt ha hb) ?_ ?_
    · intro N
      refine ((finite_degree_lt N).prod (finite_degree_lt N)).subset ?_
      rintro ⟨d, e⟩ ⟨hne, hlt⟩
      simp only [Set.mem_prod, Set.mem_ofPred_eq]
      refine ⟨?_, hlt⟩
      by_contra hge
      push Not at hge
      apply hne
      simp only [Function.uncurry_apply_pair, hT]
      rw [coeff_mono_eq_zero hs0 ht0 (lt_of_lt_of_le hlt hge)]
      simp
    · rintro ⟨d, e⟩
      simp only [Function.uncurry_apply_pair, hT, norm_mul]
      have h1 := hG d
      have h2 := hM d e
      have h3 := norm_mono_le (le_max_left ‖a‖ ‖b‖) (le_max_right ‖a‖ ‖b‖) e
      rw [norm_mul] at h3
      calc ‖MvPowerSeries.coeff d G‖ * (‖MvPowerSeries.coeff e (M d)‖ * (‖a ^ (e 0)‖ * ‖b ^ (e 1)‖))
          ≤ 1 * (1 * max ‖a‖ ‖b‖ ^ e.degree) := by gcongr
        _ = _ := by ring
  have hL : evalMv2 (G.subst ![s, t]) a b = ∑' e, ∑' d, T d e := by
    rw [evalMv2_eq]
    congr 1; funext e
    have hfin : (Function.support fun d => MvPowerSeries.coeff d G *
        MvPowerSeries.coeff e (M d)).Finite := by
      refine (finite_degree_lt (e.degree + 1)).subset ?_
      intro d hd
      simp only [Set.mem_ofPred_eq]
      by_contra hge
      apply hd
      simp only [hMdef]
      rw [coeff_mono_eq_zero hs0 ht0 (by omega : e.degree < d.degree), mul_zero]
    have hfin' : (Function.support fun d => T d e).Finite := by
      refine hfin.subset ?_
      intro d hd h0
      apply hd
      have h0' : MvPowerSeries.coeff d G * MvPowerSeries.coeff e (M d) = 0 := h0
      simp only [hT]
      rw [← mul_assoc, h0', zero_mul]
    unfold term
    rw [coeff_subst_two G s t hs0 ht0 e, finsum_mul, tsum_eq_finsum hfin']
    congr 1; funext d
    simp only [hT, hMdef]; ring
  have hR : evalMv2 G (evalMv2 s a b) (evalMv2 t a b) = ∑' d, ∑' e, T d e := by
    rw [evalMv2_eq G (evalMv2 s a b) (evalMv2 t a b)]
    congr 1; funext d
    simp only [hT, term]
    rw [tsum_mul_left, ← hMev d, evalMv2_eq]
    rfl
  rw [hL, hR, hsum.tsum_comm]

theorem evalMv2_zero' (a b : K) : evalMv2 (0 : MvPowerSeries (Fin 2) K) a b = 0 := by
  simp [evalMv2]

theorem ne_zero_of_eval {p : MvPowerSeries (Fin 2) K} {a b : K} (h : evalMv2 p a b ≠ 0) : p ≠ 0 := by
  rintro rfl; exact h (evalMv2_zero' a b)

theorem evalMv2_sub {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (F - G) a b = evalMv2 F a b - evalMv2 G a b :=
  map_sub (ev a b ha hb) ⟨F, hF⟩ ⟨G, hG⟩

theorem evalMv2_neg {F : MvPowerSeries (Fin 2) K} (hF : IntegralMv F) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) : evalMv2 (-F) a b = -evalMv2 F a b :=
  map_neg (ev a b ha hb) ⟨F, hF⟩

theorem evalMv2_subst_X1 (w : PowerSeries K) (a b : K) :
    evalMv2 (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) a b = evalPS w b := by
  classical
  rw [evalMv2_eq, evalPS]
  have hsupp : Function.support (term (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) a b)
      ⊆ Set.range (Finsupp.single (1 : Fin 2)) := by
    intro e he
    have := WeierstrassChordSeries.coeff_Wi w 1 e
    unfold WeierstrassChordSeries.Wi at this
    by_cases h : e = Finsupp.single 1 (e 1)
    · exact ⟨e 1, h.symm⟩
    · exfalso; apply he; simp [term, this, h]
  rw [← (Finsupp.single_injective (1 : Fin 2)).tsum_eq hsupp]
  congr 1; funext n
  have := WeierstrassChordSeries.coeff_Wi w 1 (Finsupp.single 1 n)
  unfold WeierstrassChordSeries.Wi at this
  simp [term, this]

theorem integral_X (i : Fin 2) : IntegralMv (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
  classical
  intro d; rw [MvPowerSeries.coeff_X]; split_ifs <;> simp

theorem integral_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralMv (MvPowerSeries.C c : MvPowerSeries (Fin 2) K) := by
  classical
  intro d; rw [MvPowerSeries.coeff_C]; split_ifs <;> simp [hc]

theorem integral_subst2 {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) : IntegralMv (G.subst ![s, t]) := by
  intro e
  rw [coeff_subst_two G s t hs0 ht0 e]
  have hfin : (Function.support fun d => MvPowerSeries.coeff d G *
      MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1))).Finite := by
    refine (finite_degree_lt (e.degree + 1)).subset ?_
    intro d hd
    simp only [Set.mem_ofPred_eq]
    by_contra hge
    apply hd
    simp only
    rw [coeff_mono_eq_zero hs0 ht0 (by omega : e.degree < d.degree), mul_zero]
  rw [finsum_eq_sum _ hfin, ← SubstitutionCoefficientCongruence.mem_unitBall]
  refine Subring.sum_mem _ fun d _ => Subring.mul_mem _ (SubstitutionCoefficientCongruence.mem_unitBall.mpr (hG d))
    (SubstitutionCoefficientCongruence.mem_unitBall.mpr ?_)
  exact SubstitutionCoefficientCongruence.integral_mul (SubstitutionCoefficientCongruence.integral_pow hs _) (SubstitutionCoefficientCongruence.integral_pow ht _) e

theorem exists_inv_integral {E : MvPowerSeries (Fin 2) K} (hE : IntegralMv E)
    (h1 : MvPowerSeries.constantCoeff E = 1) : ∃ ψ, IntegralMv ψ ∧ E * ψ = 1 := by
  let EU : MvPowerSeries (Fin 2) (unitBall K) := fun d => ⟨MvPowerSeries.coeff d E, hE d⟩
  have hmap : MvPowerSeries.map (unitBall K).subtype EU = E := by
    ext d; rw [MvPowerSeries.coeff_map]; rfl
  have hc : MvPowerSeries.constantCoeff EU = 1 := by
    apply Subtype.ext
    have : MvPowerSeries.constantCoeff E = 1 := h1
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this ⊢
    exact this
  obtain ⟨v, hv⟩ := MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hc]; exact isUnit_one)
  refine ⟨MvPowerSeries.map (unitBall K).subtype ↑v⁻¹, fun d => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact (MvPowerSeries.coeff d (↑v⁻¹ : MvPowerSeries (Fin 2) (unitBall K))).2
  · rw [← hmap, ← map_mul, ← hv, Units.mul_inv, map_one]

end Analysis

def chordPX {R : Type*} [CommRing R] (a1 a2 z1 z2 w1 w2 c v : R) : R :=
  c * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2 - v * ((w1 - w2) ^ 2 * w1 * w2
    + a1 * (w1 - w2) * (z1 * w2 - z2 * w1) * w1 * w2 - a2 * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2
    - z1 * (z1 * w2 - z2 * w1) ^ 2 * w2 - z2 * (z1 * w2 - z2 * w1) ^ 2 * w1)

def chordPY {R : Type*} [CommRing R] (a1 a3 z1 z2 w1 w2 c v : R) : R :=
  (z1 * w2 - z2 * w1) * w1 - (w1 - w2) * (c * w1 - z1 * v) + (z1 * w2 - z2 * w1) * v
    - a1 * c * (z1 * w2 - z2 * w1) * w1 - a3 * v * (z1 * w2 - z2 * w1) * w1

def tanPX {R : Type*} [CommRing R] (a1 a2 a3 a4 z w c v : R) : R :=
  c * w ^ 2 * (-2 + a1 * z + a3 * w) ^ 2 - v * ((3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) ^ 2
    + a1 * (3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) * w * (-2 + a1 * z + a3 * w)
    - a2 * w ^ 2 * (-2 + a1 * z + a3 * w) ^ 2 - 2 * z * w * (-2 + a1 * z + a3 * w) ^ 2)

def tanPY {R : Type*} [CommRing R] (a1 a2 a3 a4 z w c v : R) : R :=
  w ^ 2 * (-2 + a1 * z + a3 * w) - (3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) * (c * w - z * v)
    + v * w * (-2 + a1 * z + a3 * w) - a1 * c * w ^ 2 * (-2 + a1 * z + a3 * w)
    - a3 * v * w ^ 2 * (-2 + a1 * z + a3 * w)

section Field

variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)

theorem chord_slope {z1 z2 w1 w2 : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) :
    (-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2) = (w1 - w2) / (z1 * w2 - z2 * w1) := by
  have h : z1 / w1 - z2 / w2 = (z1 * w2 - z2 * w1) / (w1 * w2) := by field_simp
  rw [h]
  field_simp
  ring

theorem chord_x_id {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (c / v - W.addX (z1 / w1) (z2 / w2) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2)))
      * (v * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2) = chordPX W.a₁ W.a₂ z1 z2 w1 w2 c v := by
  rw [chord_slope hw1 hw2 hN, WeierstrassCurve.Affine.addX, chordPX]
  generalize z1 * w2 - z2 * w1 = N at *
  field_simp
  try ring

theorem chord_y_id {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (-1 / v - W.negY (c / v) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2) * (c / v - z1 / w1)
      + -1 / w1)) * (v * (z1 * w2 - z2 * w1) * w1) = - chordPY W.a₁ W.a₃ z1 z2 w1 w2 c v := by
  rw [chord_slope hw1 hw2 hN, WeierstrassCurve.Affine.negY, chordPY]
  generalize z1 * w2 - z2 * w1 = N at *
  field_simp
  ring

theorem tan_slope {z w : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) :
    (3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) =
    (3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w) / (w * (-2 + W.a₁ * z + W.a₃ * w)) := by
  have h : -1 / w - W.negY (z / w) (-1 / w) = (-2 + W.a₁ * z + W.a₃ * w) / w := by
    rw [WeierstrassCurve.Affine.negY]; field_simp; ring
  rw [h]
  field_simp
  ring

theorem tan_x_id {z w c v : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hv : v ≠ 0) :
    (c / v - W.addX (z / w) (z / w) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)))) * (v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w) ^ 2)
      = tanPX W.a₁ W.a₂ W.a₃ W.a₄ z w c v := by
  rw [tan_slope W hw hM, WeierstrassCurve.Affine.addX, tanPX]
  generalize 3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w = Nt
  generalize -2 + W.a₁ * z + W.a₃ * w = M at *
  field_simp
  ring

theorem tan_y_id {z w c v : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hv : v ≠ 0) :
    (-1 / v - W.negY (c / v) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) * (c / v - z / w) + -1 / w))
      * (v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w)) = - tanPY W.a₁ W.a₂ W.a₃ W.a₄ z w c v := by
  rw [tan_slope W hw hM, WeierstrassCurve.Affine.negY, tanPY]
  generalize 3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w = Nt
  generalize -2 + W.a₁ * z + W.a₃ * w = M at *
  field_simp
  try ring

theorem chord_iff {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (c / v = W.addX (z1 / w1) (z2 / w2) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2)) ∧
      -1 / v = W.addY (z1 / w1) (z2 / w2) (-1 / w1) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2))) ↔
    (chordPX W.a₁ W.a₂ z1 z2 w1 w2 c v = 0 ∧ chordPY W.a₁ W.a₃ z1 z2 w1 w2 c v = 0) := by
  have hk1 : v * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2 ≠ 0 := by
    have := pow_ne_zero 2 hN; positivity
  have hk2 : v * (z1 * w2 - z2 * w1) * w1 ≠ 0 := by positivity
  have eX := chord_x_id W hw1 hw2 hN hv (c := c)
  have eY := chord_y_id W hw1 hw2 hN hv (c := c)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← eX, h1, sub_self, zero_mul], ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1] at h2
    rw [h2, sub_self, zero_mul] at eY
    exact neg_eq_zero.mp eY.symm
  · rintro ⟨h1, h2⟩
    rw [← eX] at h1
    have h1' := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hk1)
    refine ⟨h1', ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1']
    rw [h2, neg_zero] at eY
    exact sub_eq_zero.mp ((mul_eq_zero.mp eY).resolve_right hk2)

theorem tan_iff {z w c v : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hv : v ≠ 0) :
    (c / v = W.addX (z / w) (z / w) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w))) ∧
      -1 / v = W.addY (z / w) (z / w) (-1 / w) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄
        - W.a₁ * (-1 / w)) / (-1 / w - W.negY (z / w) (-1 / w)))) ↔
    (tanPX W.a₁ W.a₂ W.a₃ W.a₄ z w c v = 0 ∧ tanPY W.a₁ W.a₂ W.a₃ W.a₄ z w c v = 0) := by
  have hk1 : v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w) ^ 2 ≠ 0 := by positivity
  have hk2 : v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w) ≠ 0 := by positivity
  have eX := tan_x_id W hw hM hv (c := c)
  have eY := tan_y_id W hw hM hv (c := c)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← eX, h1, sub_self, zero_mul], ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1] at h2
    rw [h2, sub_self, zero_mul] at eY
    exact neg_eq_zero.mp eY.symm
  · rintro ⟨h1, h2⟩
    rw [← eX] at h1
    have h1' := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hk1)
    refine ⟨h1', ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1']
    rw [h2, neg_zero] at eY
    exact sub_eq_zero.mp ((mul_eq_zero.mp eY).resolve_right hk2)

end Field

def mP {R : Type*} [CommRing R] (a1 a3 z w : R) : R := -2 + a1 * z + a3 * w

def weqP {R : Type*} [CommRing R] (a1 a2 a3 a4 a6 s v : R) : R :=
  v - (s ^ 3 + a1 * (s * v) + a2 * (s ^ 2 * v) + a3 * v ^ 2 + a4 * (s * v ^ 2) + a6 * v ^ 3)

section Maps

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_chordPX (a1 a2 z1 z2 w1 w2 c v : R) :
    f (chordPX a1 a2 z1 z2 w1 w2 c v) = chordPX (f a1) (f a2) (f z1) (f z2) (f w1) (f w2) (f c) (f v) := by
  simp only [chordPX, map_sub, map_add, map_mul, map_pow]

theorem map_chordPY (a1 a3 z1 z2 w1 w2 c v : R) :
    f (chordPY a1 a3 z1 z2 w1 w2 c v) = chordPY (f a1) (f a3) (f z1) (f z2) (f w1) (f w2) (f c) (f v) := by
  simp only [chordPY, map_sub, map_add, map_mul, map_pow]

theorem map_tanPX (a1 a2 a3 a4 z w c v : R) :
    f (tanPX a1 a2 a3 a4 z w c v) = tanPX (f a1) (f a2) (f a3) (f a4) (f z) (f w) (f c) (f v) := by
  simp only [tanPX, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem map_tanPY (a1 a2 a3 a4 z w c v : R) :
    f (tanPY a1 a2 a3 a4 z w c v) = tanPY (f a1) (f a2) (f a3) (f a4) (f z) (f w) (f c) (f v) := by
  simp only [tanPY, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem map_weqP (a1 a2 a3 a4 a6 s v : R) :
    f (weqP a1 a2 a3 a4 a6 s v) = weqP (f a1) (f a2) (f a3) (f a4) (f a6) (f s) (f v) := by
  simp only [weqP, map_sub, map_add, map_mul, map_pow]

theorem map_mP (a1 a3 z w : R) : f (mP a1 a3 z w) = mP (f a1) (f a3) (f z) (f w) := by
  simp only [mP, map_add, map_mul, map_neg, map_ofNat]

end Maps

section Formal

variable {K : Type u} [Field K]

theorem subst_XX (G : MvPowerSeries (Fin 2) K) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] = G := by
  have : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext i; fin_cases i <;> rfl
  rw [this, MvPowerSeries.subst_self]; rfl

theorem hasSubst2 {s t : MvPowerSeries (Fin 2) K} (hs : MvPowerSeries.constantCoeff s = 0)
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.HasSubst ![s, t] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])

theorem cc_subst2 {G s t : MvPowerSeries (Fin 2) K} (hG : MvPowerSeries.constantCoeff G = 0)
    (hs : MvPowerSeries.constantCoeff s = 0) (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.constantCoeff (G.subst ![s, t]) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst2 hs ht)
    (by intro i; fin_cases i <;> simp [hs, ht]) hG

theorem cc_wsubst {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) {σ : Type}
    {s : MvPowerSeries σ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  obtain ⟨u0, hwu, _⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  rw [WeierstrassCoordinateSubstitution.subst_w hwu s hs, map_mul, map_pow, hs]; simp

theorem fg_ne_zero (F : FormalGroup K) : F.toPowerSeries ≠ 0 := by
  intro h; have := F.lin_coeff_X; rw [h] at this; simp at this

theorem x_X0_ne_formal_group {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w)
    (F : FormalGroup K) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w F.toPowerSeries := by
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hφ : MvPowerSeries.HasSubst
      ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := hasSubst2 (by simp) (by simp)
  refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) _ _ (by simp)
    F.zero_constantCoeff (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (fg_ne_zero F) ?_ ?_
  · rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]; rfl
  · rw [MvPowerSeries.coe_substAlgHom,
      F.zero_add (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    exact WeierstrassCoordinateSubstitution.X_ne_zero' 1

theorem x_X0_ne_x_X1 {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w (MvPowerSeries.X 1) := by
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hφ : MvPowerSeries.HasSubst
      ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := hasSubst2 (by simp) (by simp)
  refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) _ _ (by simp)
    (by simp) (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (WeierstrassCoordinateSubstitution.X_ne_zero' 1) ?_ ?_
  · rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]; rfl
  · rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]
    exact WeierstrassCoordinateSubstitution.X_ne_zero' 1

theorem weq_C {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K} (h : WEqAt W s v) :
    v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3 := by
  unfold WEqAt at h
  simpa only [MvPowerSeries.smul_eq_C_mul] using h

theorem weq_of_C {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K}
    (h : v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3) : WEqAt W s v := by
  unfold WEqAt
  simpa only [MvPowerSeries.smul_eq_C_mul] using h

theorem inv_formal (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (ψ : MvPowerSeries (Fin 2) K)
    (hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * ψ = 1) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      -MvPowerSeries.X 0 * ψ] = 0 := by
  classical
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  set w0 := w.subst z0 with hw0
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have n0 : z0 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 0
  have n1 : z1 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have cw0 : MvPowerSeries.constantCoeff w0 = 0 := cc_wsubst hw c0
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have nG : G ≠ 0 := fg_ne_zero F
  set E := 1 - MvPowerSeries.C W.a₁ * z0 - MvPowerSeries.C W.a₃ * w0 with hE
  have nE : E ≠ 0 := left_ne_zero_of_mul_eq_one hψ
  have nψ : ψ ≠ 0 := right_ne_zero_of_mul_eq_one hψ
  set J := -z0 * ψ with hJ
  have cJ : MvPowerSeries.constantCoeff J = 0 := by simp [hJ, c0]
  have nJ : J ≠ 0 := by
    rw [hJ, neg_mul, neg_ne_zero]; exact mul_ne_zero n0 nψ
  have hW0 := weq_C (hU K W w hw (Fin 2) z0 c0).1
  have hwJ : w.subst J = -w0 * ψ := by
    obtain ⟨_, huniq⟩ := hU K W w hw (Fin 2) J cJ
    refine (huniq _ (by simp [cw0]) (weq_of_C ?_)).symm
    have key : E ^ 3 * ((-w0 * ψ) - (J ^ 3 + MvPowerSeries.C W.a₁ * (J * (-w0 * ψ))
        + MvPowerSeries.C W.a₂ * (J ^ 2 * (-w0 * ψ)) + MvPowerSeries.C W.a₃ * (-w0 * ψ) ^ 2
        + MvPowerSeries.C W.a₄ * (J * (-w0 * ψ) ^ 2) + MvPowerSeries.C W.a₆ * (-w0 * ψ) ^ 3)) = 0 := by
      rw [hJ]
      linear_combination ((z0 ^ 3 + MvPowerSeries.C W.a₂ * (z0 ^ 2 * w0)
          + MvPowerSeries.C W.a₄ * (z0 * w0 ^ 2) + MvPowerSeries.C W.a₆ * w0 ^ 3)
          * ((E * ψ) ^ 2 + E * ψ + 1)
        - (MvPowerSeries.C W.a₁ * (z0 * w0) + MvPowerSeries.C W.a₃ * w0 ^ 2) * E * (E * ψ + 1)
        - w0 * E ^ 2) * hψ - hW0 - (1 + E) * w0 * hE
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 nE))
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have nw0 : w0 ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) z0 c0).1 n0
  have hjC : ∀ a : K, algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) a =
      j (MvPowerSeries.C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K), MvPowerSeries.algebraMap_apply]
    rfl
  have hjψ : j ψ = (j E)⁻¹ := WeierstrassSubstitution.eq_inv_of_map j hψ
  have hjE : j E = 1 - j (MvPowerSeries.C W.a₁) * j z0 - j (MvPowerSeries.C W.a₃) * j w0 := by
    rw [hE]; simp only [map_sub, map_one, map_mul]
  have hxJ : xOf w J = xOf w z0 := by
    unfold xOf
    rw [hwJ, hJ, map_mul, map_mul, map_neg, map_neg, neg_mul, neg_mul, neg_div_neg_eq,
      mul_div_mul_right _ _ (jne nψ)]
  have hyJ : yOf w J = (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
      (xOf w z0) (yOf w z0) := by
    unfold yOf xOf
    rw [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, hjC, hjC,
      hwJ, map_mul, map_neg, hjψ]
    have h1 := jne nw0
    have h2 := jne nE
    rw [hjE] at h2 ⊢
    simp only [← hj, ← hw0]
    field_simp

  have p0 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z0 c0 n0
  have p1 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z1 c1 n1
  have pJ := wSeriesNonsingularPoint_holds K W w hw (Fin 2) J cJ nJ
  have hPJ : WeierstrassCurve.Affine.Point.some _ _ pJ = -WeierstrassCurve.Affine.Point.some _ _ p0 := by
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hxJ, hyJ⟩
  obtain ⟨pG, eG⟩ := WeierstrassCoordinateSubstitution.chord_add z0 z1 G p0 p1 (x_X0_ne_x_X1 hw) hch
  have xGJ : xOf w G ≠ xOf w J := by rw [hxJ]; exact (x_X0_ne_formal_group hw F).symm
  have chGJ := hS K W w hw G cG hch (Fin 2) G J cG cJ nG nJ xGJ
  obtain ⟨pH, eH⟩ := WeierstrassCoordinateSubstitution.chord_add G J _ pG pJ xGJ chGJ
  have hH : WeierstrassCurve.Affine.Point.some _ _ pH = WeierstrassCurve.Affine.Point.some _ _ p1 := by
    rw [← eH, hPJ, ← eG]; abel
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hH
  have hGJ := hasSubst2 cG cJ
  have hHz1 : G.subst ![G, J] = z1 :=
    WeierstrassCoordinateSubstitution.eq_of_xy hwu hu _ _ (cc_subst2 cG cG cJ) c1 hx hy

  have hφ : MvPowerSeries.HasSubst ![z0, (0 : MvPowerSeries (Fin 2) K)] := hasSubst2 c0 (by simp)
  have hφz0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] z0 = z0 := by
    rw [hz0, MvPowerSeries.subst_X hφ]; rfl
  have hφw0 : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] w0 = w0 := by
    rw [hw0, WeierstrassSubstitution.mvsubst_psubst w z0 c0 _ hφ, hφz0]
  have hφE : MvPowerSeries.substAlgHom hφ E = E := by
    rw [hE, map_sub, map_sub, map_one, map_mul, map_mul, MvPowerSeries.coe_substAlgHom, hφz0,
      hφw0]
    simp
  have hφψ : MvPowerSeries.substAlgHom hφ ψ = ψ := by
    have h := congrArg (MvPowerSeries.substAlgHom hφ) hψ
    rw [map_mul, map_one, hφE, ← hψ] at h
    exact mul_left_cancel₀ nE h
  have hφJ : MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] J = J := by
    rw [← MvPowerSeries.coe_substAlgHom hφ, hJ, map_mul, map_neg, hφψ,
      MvPowerSeries.coe_substAlgHom, hφz0]
  have e := congrArg (MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)]) hHz1
  rw [MvPowerSeries.subst_comp_subst_apply hGJ hφ, hz1, MvPowerSeries.subst_X hφ] at e
  have e2 : (fun i => MvPowerSeries.subst ![z0, (0 : MvPowerSeries (Fin 2) K)] (![G, J] i)) =
      ![z0, J] := by
    funext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero c0)
    · simpa using hφJ
  rw [e2] at e
  simpa using e

theorem dbl_formal (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (hy : yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] ≠ 0 ∧
    xOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addX
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) ∧
    yOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) := by
  classical
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have n0 : z0 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 0
  have n1 : z1 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 1
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have nG : G ≠ 0 := fg_ne_zero F
  set D := G.subst ![z0, z0] with hD
  have cD : MvPowerSeries.constantCoeff D = 0 := cc_subst2 cG c0 c0
  have p0 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z0 c0 n0
  have p1 := wSeriesNonsingularPoint_holds K W w hw (Fin 2) z1 c1 n1
  obtain ⟨pG, eG⟩ := WeierstrassCoordinateSubstitution.chord_add z0 z1 G p0 p1 (x_X0_ne_x_X1 hw) hch
  have x0G := x_X0_ne_formal_group hw F
  have chH := hS K W w hw G cG hch (Fin 2) z0 G c0 cG n0 nG x0G
  obtain ⟨pH, eH⟩ := WeierstrassCoordinateSubstitution.chord_add z0 G _ p0 pG x0G chH
  have h0s : PowerSeries.HasSubst z0 := PowerSeries.HasSubst.of_constantCoeff_zero c0
  have h1s : PowerSeries.HasSubst z1 := PowerSeries.HasSubst.of_constantCoeff_zero c1
  have hassoc : G.subst ![D, z1] = G.subst ![z0, G] := by
    have := F.assoc' h0s h0s h1s
    rw [← hG] at this
    rw [hD, this, hz0, hz1, subst_XX]
  by_cases hD0 : D = 0
  · exfalso
    have hHz : G.subst ![z0, G] = z1 := by
      rw [← hassoc, hD0]; exact F.zero_add h1s
    have e1 : WeierstrassCurve.Affine.Point.some _ _ pH =
        WeierstrassCurve.Affine.Point.some _ _ p1 := by
      rw [WeierstrassCurve.Affine.Point.some.injEq, hHz]; exact ⟨rfl, rfl⟩
    rw [e1, ← eG] at eH
    have h2 : WeierstrassCurve.Affine.Point.some _ _ p0 + WeierstrassCurve.Affine.Point.some _ _ p0 = 0 := by
      calc _ = (WeierstrassCurve.Affine.Point.some _ _ p0 + (WeierstrassCurve.Affine.Point.some _ _ p0 +
              WeierstrassCurve.Affine.Point.some _ _ p1)) - WeierstrassCurve.Affine.Point.some _ _ p1 := by
            abel
        _ = 0 := by rw [eH, sub_self]
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h3
    exact hy h3.2
  · refine ⟨hD0, ?_⟩
    have hφ : MvPowerSeries.HasSubst ![(0 : MvPowerSeries (Fin 2) K), z1] := hasSubst2 (by simp) c1
    have xD1 : xOf w D ≠ xOf w z1 := by
      refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) D z1 cD c1 hD0 n1 ?_ ?_
      · rw [MvPowerSeries.coe_substAlgHom, hD, MvPowerSeries.subst_comp_subst_apply
          (hasSubst2 c0 c0) hφ]
        have e2 : (fun i => MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) K), z1] (![z0, z0] i)) =
            (0 : Fin 2 → MvPowerSeries (Fin 2) K) := by
          funext i; fin_cases i <;> simp [hz0, MvPowerSeries.subst_X hφ]
        rw [e2]
        exact MvPowerSeries.subst_zero_of_constantCoeff_zero cG
      · rw [MvPowerSeries.coe_substAlgHom, hz1, MvPowerSeries.subst_X hφ]; simpa using n1
    have pD := wSeriesNonsingularPoint_holds K W w hw (Fin 2) D cD hD0
    have chD := hS K W w hw G cG hch (Fin 2) D z1 cD c1 hD0 n1 xD1
    obtain ⟨pK, eK⟩ := WeierstrassCoordinateSubstitution.chord_add D z1 _ pD p1 xD1 chD
    have e1 : WeierstrassCurve.Affine.Point.some _ _ pK =
        WeierstrassCurve.Affine.Point.some _ _ pH := by
      rw [WeierstrassCurve.Affine.Point.some.injEq, hassoc]; exact ⟨rfl, rfl⟩
    rw [e1, ← eH, ← eG] at eK
    have h2 : WeierstrassCurve.Affine.Point.some _ _ pD =
        WeierstrassCurve.Affine.Point.some _ _ p0 + WeierstrassCurve.Affine.Point.some _ _ p0 := by
      have := eK
      rw [← add_assoc] at this
      exact add_right_cancel this
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.Affine.Point.some.injEq,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hy] at h2
    exact h2

end Formal

section Main

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem evalMv2_chordPX {a1 a2 z1 z2 w1 w2 c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv z1) (h4 : IntegralMv z2) (h5 : IntegralMv w1)
    (h6 : IntegralMv w2) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (chordPX a1 a2 z1 z2 w1 w2 c v) a b = chordPX (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 z1 a b) (evalMv2 z2 a b) (evalMv2 w1 a b) (evalMv2 w2 a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_chordPX (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨z1, h3⟩ ⟨z2, h4⟩ ⟨w1, h5⟩ ⟨w2, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩

theorem evalMv2_chordPY {a1 a3 z1 z2 w1 w2 c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a3) (h3 : IntegralMv z1) (h4 : IntegralMv z2) (h5 : IntegralMv w1)
    (h6 : IntegralMv w2) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (chordPY a1 a3 z1 z2 w1 w2 c v) a b = chordPY (evalMv2 a1 a b) (evalMv2 a3 a b)
      (evalMv2 z1 a b) (evalMv2 z2 a b) (evalMv2 w1 a b) (evalMv2 w2 a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_chordPY (ev a b ha hb) ⟨a1, h1⟩ ⟨a3, h2⟩ ⟨z1, h3⟩ ⟨z2, h4⟩ ⟨w1, h5⟩ ⟨w2, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩

theorem evalMv2_tanPX {a1 a2 a3 a4 z w c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv a3) (h4 : IntegralMv a4) (h5 : IntegralMv z)
    (h6 : IntegralMv w) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (tanPX a1 a2 a3 a4 z w c v) a b = tanPX (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 a3 a b) (evalMv2 a4 a b) (evalMv2 z a b) (evalMv2 w a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_tanPX (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨a3, h3⟩ ⟨a4, h4⟩ ⟨z, h5⟩ ⟨w, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩

theorem evalMv2_tanPY {a1 a2 a3 a4 z w c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv a3) (h4 : IntegralMv a4) (h5 : IntegralMv z)
    (h6 : IntegralMv w) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (tanPY a1 a2 a3 a4 z w c v) a b = tanPY (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 a3 a b) (evalMv2 a4 a b) (evalMv2 z a b) (evalMv2 w a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_tanPY (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨a3, h3⟩ ⟨a4, h4⟩ ⟨z, h5⟩ ⟨w, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩

theorem evalMv2_weqP {a1 a2 a3 a4 a6 s v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv a3) (h4 : IntegralMv a4) (h5 : IntegralMv a6)
    (h6 : IntegralMv s) (h7 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (weqP a1 a2 a3 a4 a6 s v) a b = weqP (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 a3 a b) (evalMv2 a4 a b) (evalMv2 a6 a b) (evalMv2 s a b) (evalMv2 v a b) :=
  map_weqP (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨a3, h3⟩ ⟨a4, h4⟩ ⟨a6, h5⟩ ⟨s, h6⟩ ⟨v, h7⟩

theorem evalMv2_mP {a1 a3 z w : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a3) (h3 : IntegralMv z) (h4 : IntegralMv w) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (mP a1 a3 z w) a b = mP (evalMv2 a1 a b) (evalMv2 a3 a b) (evalMv2 z a b) (evalMv2 w a b) :=
  map_mP (ev a b ha hb) ⟨a1, h1⟩ ⟨a3, h2⟩ ⟨z, h3⟩ ⟨w, h4⟩

theorem w_integral {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) (n : ℕ) : ‖coeff n w‖ ≤ 1 := by
  have hsub : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆
      (subalgebraOfSubring (unitBall K) : Set K) := by
    obtain ⟨h1, h2, h3, h4, h6⟩ := hW
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_subalgebraOfSubring, SubstitutionCoefficientCongruence.mem_unitBall]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  exact SubstitutionCoefficientCongruence.mem_unitBall.mp
    (mem_subalgebraOfSubring.mp (Algebra.adjoin_le hsub (WeierstrassChordSeries.w_coeff_mem hw n)))

theorem weierstrassPolynomial_eq_zero_of_equation {W : WeierstrassCurve K} {s v : MvPowerSeries (Fin 2) K} (h : WEqAt W s v) :
    weqP (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) s v = 0 := by
  rw [weqP]; exact sub_eq_zero.mpr (weq_C h)

theorem eq_zero_of_weqP {a1 a2 a3 a4 a6 c : K} (h : weqP a1 a2 a3 a4 a6 c 0 = 0) : c = 0 := by
  simp only [weqP] at h
  have : c ^ 3 = 0 := by linear_combination -h
  exact pow_eq_zero_iff (by norm_num) |>.mp this

theorem eval_zero_left (F : FormalGroup K) (hF : IntegralMv F.toPowerSeries) {b : K}
    (hb : ‖b‖ < 1) : evalMv2 F.toPowerSeries 0 b = b := by
  have h := evalMv2_subst hF (s := 0) (t := MvPowerSeries.X 1) (fun d => by simp) (integral_X 1)
    (by simp) (by simp) (a := 0) (b := b) (by simp) hb
  rw [F.zero_add (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), evalMv2_X1, evalMv2_zero'] at h
  exact h.symm

theorem eval_zero_right (F : FormalGroup K) (hF : IntegralMv F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) : evalMv2 F.toPowerSeries a 0 = a := by
  have h := evalMv2_subst hF (s := MvPowerSeries.X 0) (t := 0) (integral_X 0) (fun d => by simp)
    (by simp) (by simp) (a := a) (b := 0) ha (by simp)
  rw [F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), evalMv2_X0, evalMv2_zero'] at h
  exact h.symm

theorem hjC_lemma {σ : Type} (a : K) :
    algebraMap K (FractionRing (MvPowerSeries σ K)) a =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (MvPowerSeries.C a) := by
  rw [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K), MvPowerSeries.algebraMap_apply]
  rfl

end Main

section Cases

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem case_chord (hU : WSubstUnique.{u}) {W : WeierstrassCurve K} {w : PowerSeries K}
    (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a b : K}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hwa : evalPS w a ≠ 0) (hwb : evalPS w b ≠ 0)
    (hN : a * evalPS w b - b * evalPS w a ≠ 0) :
    -(W.toAffine.addX (a / evalPS w a) (b / evalPS w b)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b))) /
      W.toAffine.addY (a / evalPS w a) (b / evalPS w b) (-1 / evalPS w a)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b)) =
      evalMv2 F.toPowerSeries a b := by
  classical
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set z1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hz1
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have c1 : MvPowerSeries.constantCoeff z1 = 0 := by simp [hz1]
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have iz0 : IntegralMv z0 := integral_X 0
  have iz1 : IntegralMv z1 := integral_X 1
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  have iw1 : IntegralMv (w.subst z1) := SubstitutionCoefficientCongruence.integral_subst hwI c1 iz1
  have iwG : IntegralMv (w.subst G) := SubstitutionCoefficientCongruence.integral_subst hwI cG hFi
  have ez0 : evalMv2 z0 a b = a := evalMv2_X0 a b
  have ez1 : evalMv2 z1 a b = b := evalMv2_X1 a b
  have ew0 : evalMv2 (w.subst z0) a b = evalPS w a := evalMv2_subst_X0 w a b
  have ew1 : evalMv2 (w.subst z1) a b = evalPS w b := evalMv2_subst_X1 w a b
  have nw0 : w.subst z0 ≠ 0 := ne_zero_of_eval (a := a) (b := b) (by rw [ew0]; exact hwa)
  have nw1 : w.subst z1 ≠ 0 := ne_zero_of_eval (a := a) (b := b) (by rw [ew1]; exact hwb)
  have nN : z0 * w.subst z1 - z1 * w.subst z0 ≠ 0 := by
    refine ne_zero_of_eval (a := a) (b := b) ?_
    rw [evalMv2_sub (SubstitutionCoefficientCongruence.integral_mul iz0 iw1) (SubstitutionCoefficientCongruence.integral_mul iz1 iw0) ha hb,
      evalMv2_mul iz0 iw1 ha hb, evalMv2_mul iz1 iw0 ha hb, ez0, ez1, ew0, ew1]
    exact hN
  have nwG : w.subst G ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) G cG).1 (fg_ne_zero F)
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have hjN : j z0 * j (w.subst z1) - j z1 * j (w.subst z0) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact jne nN
  unfold ChordAt xOf yOf at hch
  obtain ⟨hX, hY⟩ := (chord_iff (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
    (jne nw0) (jne nw1) hjN (jne nwG)).mp hch
  rw [show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) from hjC_lemma _,
    show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂ =
      j (MvPowerSeries.C W.a₂) from hjC_lemma _, ← map_chordPX] at hX
  rw [show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) from hjC_lemma _,
    show (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ =
      j (MvPowerSeries.C W.a₃) from hjC_lemma _, ← map_chordPY] at hY
  have hX' := hinj (hX.trans (map_zero j).symm)
  have hY' := hinj (hY.trans (map_zero j).symm)
  have hWq := weierstrassPolynomial_eq_zero_of_equation (hU K W w hw (Fin 2) G cG).1
  have eX := evalMv2_chordPX (integral_C h1) (integral_C h2) iz0 iz1 iw0 iw1 hFi iwG ha hb
  have eY := evalMv2_chordPY (integral_C h1) (integral_C h3) iz0 iz1 iw0 iw1 hFi iwG ha hb
  have eW := evalMv2_weqP (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4)
    (integral_C h6) hFi iwG ha hb
  rw [hX', evalMv2_zero'] at eX
  rw [hY', evalMv2_zero'] at eY
  rw [hWq, evalMv2_zero'] at eW
  simp only [evalMv2_C, ez0, ez1, ew0, ew1] at eX eY eW
  set c := evalMv2 G a b with hc
  set v := evalMv2 (w.subst G) a b with hv
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at eW eY
    have hc0 := eq_zero_of_weqP eW.symm
    rw [hc0] at eY
    apply mul_ne_zero hN hwa
    simp only [chordPY] at eY
    linear_combination -eY
  have hK := (chord_iff W.toAffine hwa hwb hN hv0 (c := c)).mpr ⟨eX.symm, eY.symm⟩
  rw [← hK.1, ← hK.2]
  field_simp

theorem case_tan (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K)
    (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) (hwa : evalPS w a ≠ 0) (hM : -2 + W.a₁ * a + W.a₃ * evalPS w a ≠ 0) :
    -(W.toAffine.addX (a / evalPS w a) (a / evalPS w a)
        ((3 * (a / evalPS w a) ^ 2 + 2 * W.toAffine.a₂ * (a / evalPS w a) + W.toAffine.a₄
          - W.toAffine.a₁ * (-1 / evalPS w a)) /
          (-1 / evalPS w a - W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a)))) /
      W.toAffine.addY (a / evalPS w a) (a / evalPS w a) (-1 / evalPS w a)
        ((3 * (a / evalPS w a) ^ 2 + 2 * W.toAffine.a₂ * (a / evalPS w a) + W.toAffine.a₄
          - W.toAffine.a₁ * (-1 / evalPS w a)) /
          (-1 / evalPS w a - W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a))) =
      evalMv2 F.toPowerSeries a a := by
  classical
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have cG : MvPowerSeries.constantCoeff G = 0 := F.zero_constantCoeff
  have iz0 : IntegralMv z0 := integral_X 0
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  set D := G.subst ![z0, z0] with hD
  have cD : MvPowerSeries.constantCoeff D = 0 := cc_subst2 cG c0 c0
  have iD : IntegralMv D := integral_subst2 hFi iz0 iz0 c0 c0
  have iwD : IntegralMv (w.subst D) := SubstitutionCoefficientCongruence.integral_subst hwI cD iD
  have ez0 : evalMv2 z0 a a = a := evalMv2_X0 a a
  have ew0 : evalMv2 (w.subst z0) a a = evalPS w a := evalMv2_subst_X0 w a a
  have eD : evalMv2 D a a = evalMv2 G a a := by
    rw [hD, evalMv2_subst hFi iz0 iz0 c0 c0 ha ha, ez0]
  have nw0 : w.subst z0 ≠ 0 := ne_zero_of_eval (a := a) (b := a) (by rw [ew0]; exact hwa)
  have nM : mP (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₃) z0 (w.subst z0) ≠ 0 := by
    refine ne_zero_of_eval (a := a) (b := a) ?_
    rw [evalMv2_mP (integral_C h1) (integral_C h3) iz0 iw0 ha ha, evalMv2_C, evalMv2_C, ez0, ew0]
    exact hM
  set j := algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) with hj
  have hinj : Function.Injective j := IsFractionRing.injective _ _
  have jne : ∀ {x}, x ≠ 0 → j x ≠ 0 := fun hx h => hx (hinj (by rw [h, map_zero]))
  have hA1 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ =
      j (MvPowerSeries.C W.a₁) := hjC_lemma _
  have hA2 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂ =
      j (MvPowerSeries.C W.a₂) := hjC_lemma _
  have hA3 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ =
      j (MvPowerSeries.C W.a₃) := hjC_lemma _
  have hA4 : (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄ =
      j (MvPowerSeries.C W.a₄) := hjC_lemma _
  have hMFr : -2 + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁ * j z0
      + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₃ * j (w.subst z0)
      ≠ 0 := by
    rw [hA1, hA3]
    have := jne nM
    rwa [map_mP] at this
  have hyF : yOf w z0 ≠ (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
      (xOf w z0) (yOf w z0) := by
    intro h
    apply hMFr
    unfold yOf xOf at h
    rw [WeierstrassCurve.Affine.negY] at h
    have hw0' := jne nw0
    simp only [← hj] at h
    field_simp at h
    first | linear_combination h | linear_combination -h
  obtain ⟨nD, hxD, hyD⟩ := dbl_formal hU hS hw F hch hyF
  have nwD : w.subst D ≠ 0 := WeierstrassSubstitution.ne_zero_of_weq (hU K W w hw (Fin 2) D cD).1 nD
  unfold xOf yOf at hxD hyD
  obtain ⟨hX, hY⟩ := (tan_iff (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
    (jne nw0) hMFr (jne nwD)).mp ⟨hxD, hyD⟩
  rw [hA1, hA2, hA3, hA4, ← map_tanPX] at hX
  rw [hA1, hA2, hA3, hA4, ← map_tanPY] at hY
  have hX' := hinj (hX.trans (map_zero j).symm)
  have hY' := hinj (hY.trans (map_zero j).symm)
  have hWq := weierstrassPolynomial_eq_zero_of_equation (hU K W w hw (Fin 2) D cD).1
  have eX := evalMv2_tanPX (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4) iz0 iw0
    iD iwD ha ha
  have eY := evalMv2_tanPY (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4) iz0 iw0
    iD iwD ha ha
  have eW := evalMv2_weqP (integral_C h1) (integral_C h2) (integral_C h3) (integral_C h4)
    (integral_C h6) iD iwD ha ha
  rw [hX', evalMv2_zero'] at eX
  rw [hY', evalMv2_zero'] at eY
  rw [hWq, evalMv2_zero'] at eW
  simp only [evalMv2_C, ez0, ew0, eD] at eX eY eW
  set c := evalMv2 G a a with hc
  set v := evalMv2 (w.subst D) a a with hv
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at eW eY
    have hc0 := eq_zero_of_weqP eW.symm
    rw [hc0] at eY
    apply mul_ne_zero (pow_ne_zero 2 hwa) hM
    simp only [tanPY] at eY
    linear_combination -eY
  have hK := (tan_iff W.toAffine hwa hM hv0 (c := c)).mpr ⟨eX.symm, eY.symm⟩
  rw [← hK.1, ← hK.2]
  field_simp

theorem case_inv (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K)
    (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) (hwa : evalPS w a ≠ 0) :
    evalMv2 F.toPowerSeries a
      (-(a / evalPS w a) / W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a)) = 0 := by
  have hwI := w_integral hW hw
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  set z0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hz0
  set G := F.toPowerSeries with hG
  have c0 : MvPowerSeries.constantCoeff z0 = 0 := by simp [hz0]
  have iz0 : IntegralMv z0 := integral_X 0
  have iw0 : IntegralMv (w.subst z0) := SubstitutionCoefficientCongruence.integral_subst hwI c0 iz0
  have cw0 : MvPowerSeries.constantCoeff (w.subst z0) = 0 := cc_wsubst hw c0
  have ez0 : evalMv2 z0 a a = a := evalMv2_X0 a a
  have ew0 : evalMv2 (w.subst z0) a a = evalPS w a := evalMv2_subst_X0 w a a
  set E := 1 - MvPowerSeries.C W.a₁ * z0 - MvPowerSeries.C W.a₃ * w.subst z0 with hE
  have iE : IntegralMv E :=
    (IL K).sub_mem ((IL K).sub_mem (IL K).one_mem ((IL K).mul_mem (integral_C h1) iz0))
      ((IL K).mul_mem (integral_C h3) iw0)
  have cE : MvPowerSeries.constantCoeff E = 1 := by simp [hE, c0, cw0]
  obtain ⟨ψ, iψ, hEψ⟩ := exists_inv_integral iE cE
  have h0 := inv_formal hU hS hw F hch ψ hEψ
  have iJ : IntegralMv (-z0 * ψ) := (IL K).mul_mem ((IL K).neg_mem iz0) iψ
  have cJ : MvPowerSeries.constantCoeff (-z0 * ψ) = 0 := by simp [c0]
  have e := evalMv2_subst hFi iz0 iJ c0 cJ ha ha
  rw [h0, evalMv2_zero', ez0] at e
  have eJ : evalMv2 (-z0 * ψ) a a = -a * evalMv2 ψ a a := by
    rw [evalMv2_mul ((IL K).neg_mem iz0) iψ ha ha, evalMv2_neg iz0 ha ha, ez0]
  have eE : evalMv2 E a a * evalMv2 ψ a a = 1 := by
    rw [← evalMv2_mul iE iψ ha ha, hEψ, evalMv2_one]
  have eE' : evalMv2 E a a = 1 - W.a₁ * a - W.a₃ * evalPS w a := by
    rw [hE, evalMv2_sub ((IL K).sub_mem (IL K).one_mem ((IL K).mul_mem (integral_C h1) iz0))
      ((IL K).mul_mem (integral_C h3) iw0) ha ha, evalMv2_sub (IL K).one_mem
      ((IL K).mul_mem (integral_C h1) iz0) ha ha, evalMv2_one,
      evalMv2_mul (integral_C h1) iz0 ha ha, evalMv2_mul (integral_C h3) iw0 ha ha, evalMv2_C,
      evalMv2_C, ez0, ew0]
  have hEa : 1 - W.a₁ * a - W.a₃ * evalPS w a ≠ 0 := by
    rw [← eE']; exact left_ne_zero_of_mul_eq_one eE
  have hψa : evalMv2 ψ a a = (1 - W.a₁ * a - W.a₃ * evalPS w a)⁻¹ := by
    rw [← eE']; exact eq_inv_of_mul_eq_one_right eE
  rw [eJ, hψa] at e
  rw [show -(a / evalPS w a) / W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a) =
      -a * (1 - W.a₁ * a - W.a₃ * evalPS w a)⁻¹ from ?_]
  · exact e.symm
  · rw [WeierstrassCurve.Affine.negY]
    have : -(-1 / evalPS w a) - W.toAffine.a₁ * (a / evalPS w a) - W.toAffine.a₃ =
        (1 - W.a₁ * a - W.a₃ * evalPS w a) / evalPS w a := by
      field_simp
      try ring
    rw [this]
    field_simp

end Cases

section MainLemma

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem param_facts (hPar : FormalGroupPointsParametrisation.{u}) {W : WeierstrassCurve K} {w : PowerSeries K}
    (hW : IntegralModel W) (hw : WFixed W w) {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    ‖-x / y‖ < 1 ∧ evalPS w (-x / y) ≠ 0 ∧ x = (-x / y) / evalPS w (-x / y) ∧
      y = -1 / evalPS w (-x / y) := by
  obtain ⟨hpos, hlt, hxe, hye⟩ := (hPar K W w hW hw).2 x y h hx
  exact ⟨hlt, ((hPar K W w hW hw).1 _ hpos hlt).1, hxe, hye⟩

theorem e1hom_main (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) (hPar : FormalGroupPointsParametrisation.{u})
    {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w)
    (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    {inst : DecidableEq K} (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    uOf (P + Q) = evalMv2 F.toPowerSeries (uOf P) (uOf Q) := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · have := eval_zero_left F hFi (b := 0) (by simp)
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    exact this.symm
  · obtain ⟨hb, -, -, -⟩ := param_facts hPar hW hw h2 hQ
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    exact (eval_zero_left F hFi hb).symm
  · obtain ⟨ha, -, -, -⟩ := param_facts hPar hW hw h1 hP
    rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero]
    exact (eval_zero_right F hFi ha).symm
  · obtain ⟨ha, hwa, hxa, hya⟩ := param_facts hPar hW hw h1 hP
    obtain ⟨hb, hwb, hxb, hyb⟩ := param_facts hPar hW hw h2 hQ
    change uOf (WeierstrassCurve.Affine.Point.some x1 y1 h1 +
      WeierstrassCurve.Affine.Point.some x2 y2 h2) = evalMv2 F.toPowerSeries (-x1 / y1) (-x2 / y2)
    generalize hA : -x1 / y1 = a at ha hwa hxa hya ⊢
    generalize hB : -x2 / y2 = b at hb hwb hxb hyb ⊢
    by_cases hx : x1 = x2
    · by_cases hy : y1 = W.toAffine.negY x2 y2
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy, ← hB]
        subst hx
        have hy2 : y2 = W.toAffine.negY x1 y1 := by
          rw [hy, WeierstrassCurve.Affine.negY_negY]
        subst hy2
        change (0 : K) = _
        rw [hxa, hya]
        exact (case_inv hU hS hW hw F hFi hch ha hwa).symm
      · have hyy := WeierstrassCurve.Affine.Y_eq_of_Y_ne h1.1 h2.1 hx hy
        subst hx
        subst hyy
        have hab : b = a := by rw [← hA, ← hB]
        subst hab
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
        change -(W.toAffine.addX x1 x1 (W.toAffine.slope x1 x1 y1 y1)) /
          W.toAffine.addY x1 x1 y1 (W.toAffine.slope x1 x1 y1 y1) = _
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
        have hM : -2 + W.a₁ * b + W.a₃ * evalPS w b ≠ 0 := by
          intro hM0
          apply hy
          rw [hxa, hya, WeierstrassCurve.Affine.negY]
          field_simp
          first | linear_combination hM0 | linear_combination -hM0
        rw [hxa, hya]
        exact case_tan hU hS hW hw F hFi hch ha hwa hM
    · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
      change -(W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2)) /
        W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) = _
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
      have hN : a * evalPS w b - b * evalPS w a ≠ 0 := by
        intro h0
        apply hx
        rw [hxa, hxb]
        field_simp
        first | linear_combination h0 | linear_combination -h0
      rw [hxa, hxb, hya, hyb]
      exact case_chord hU hW hw F hFi hch ha hb hwa hwb hN

end MainLemma

end Formalism.ELL.FormalGroupPointsHom

theorem Formalism.ELL.formal_group_points_hom_of (hU : Formalism.ELL.WSubstUnique.{u}) (hS : Formalism.ELL.WChordSubst.{u})
    (hFG : Formalism.ELL.WFormalGroup.{u}) (hPar : Formalism.ELL.FormalGroupPointsParametrisation.{u}) : Formalism.ELL.FormalGroupPointsHomomorphism.{u} := by
  intro K _ _ _ W w F₂ hW hw hF₂i hF₂0 hch P Q hP hQ
  obtain ⟨F, -, hFch⟩ := hFG K W w hw
  obtain ⟨u0, hwu, hu⟩ := Formalism.ELL.WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hFeq : F₂ = F.toPowerSeries :=
    Formalism.ELL.WeierstrassCoordinateSubstitution.eq_of_xy hwu hu _ _ hF₂0 F.zero_constantCoeff (hch.1.trans hFch.1.symm)
      (hch.2.trans hFch.2.symm)
  subst hFeq
  exact Formalism.ELL.FormalGroupPointsHom.e1hom_main hU hS hPar hW hw F hF₂i hch P Q hP hQ
