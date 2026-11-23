import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities
import Formalism.DistinguishedUnitIdeals.DescentLemmasAllHold

noncomputable section

open Classical

namespace Formalism.MainNotions.ArcLiftingSetup

section R2

open PowerSeries

private def DivisibilityInvariant {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (f : PowerSeries O) (i m : ℕ) : Prop :=
  ¬ ϖ ^ (m + 1) ∣ coeff i f ∧ ∀ t : ℕ, 1 ≤ t → ϖ ^ (m + 1 - e * t) ∣ coeff (i + t) f

private lemma divisibilityInvariant_mul_linear {O : Type} [CommRing O] (ϖ c : O) (e : ℕ) (hc : ϖ ^ e ∣ c)
    (f : PowerSeries O) (i m : ℕ) (h : DivisibilityInvariant ϖ e f i m) : DivisibilityInvariant ϖ e (f * (X - C c)) (i + 1) m := by
  obtain ⟨h1, h2⟩ := h
  have hcoeff : ∀ k, coeff (k + 1) (f * (X - C c)) = coeff k f - coeff (k + 1) f * c := by
    intro k
    rw [mul_sub, map_sub, coeff_succ_mul_X, coeff_mul_C]
  refine ⟨?_, fun t ht => ?_⟩
  · rw [hcoeff]
    intro hd
    apply h1
    have h3 : ϖ ^ (m + 1) ∣ coeff (i + 1) f * c := by
      have h4 := mul_dvd_mul (h2 1 le_rfl) hc
      rw [← pow_add, mul_one] at h4
      exact (pow_dvd_pow ϖ (by omega)).trans h4
    have h5 := dvd_add hd h3
    rwa [sub_add_cancel] at h5
  · rw [show i + 1 + t = (i + t) + 1 by omega, hcoeff]
    refine dvd_sub (h2 t ht) ?_
    have h4 := mul_dvd_mul (h2 (t + 1) (by omega)) hc
    rw [← pow_add, show i + (t + 1) = i + t + 1 by omega] at h4
    refine (pow_dvd_pow ϖ ?_).trans h4
    rw [mul_add, mul_one]
    generalize e * t = u
    omega

private lemma divisibilityInvariant_mul_pow {O : Type} [CommRing O] (ϖ c : O) (e : ℕ) (hc : ϖ ^ e ∣ c)
    (f : PowerSeries O) (i m : ℕ) (h : DivisibilityInvariant ϖ e f i m) (A : ℕ) :
    DivisibilityInvariant ϖ e (f * (X - C c) ^ A) (i + A) m := by
  induction A with
  | zero => simpa using h
  | succ A ih =>
    rw [pow_succ, ← mul_assoc, show i + (A + 1) = (i + A) + 1 by omega]
    exact divisibilityInvariant_mul_linear ϖ c e hc _ _ _ ih

open Classical in
private lemma exists_divisibilityInvariant {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (he : 1 ≤ e)
    (f : PowerSeries O) (v₁ : ℕ) (h0 : ¬ ϖ ^ (e * v₁ + 1) ∣ coeff 0 f) :
    ∃ i, i ≤ v₁ ∧ DivisibilityInvariant ϖ e f i (e * (v₁ - i)) := by

  let Pr : ℕ → Prop := fun i => ¬ ϖ ^ (e * (v₁ - i) + 1) ∣ coeff i f
  have hP0 : Pr 0 := by simpa [Pr] using h0
  refine ⟨Nat.findGreatest Pr v₁, Nat.findGreatest_le v₁, Nat.findGreatest_spec (Nat.zero_le _) hP0,
    fun t ht => ?_⟩
  set i := Nat.findGreatest Pr v₁ with hi
  have hiv : i ≤ v₁ := Nat.findGreatest_le v₁
  by_cases hit : i + t ≤ v₁
  · have hn := Nat.findGreatest_is_greatest (by omega : i < i + t) hit
    obtain ⟨d, hd⟩ : ∃ d, v₁ = i + t + d := ⟨v₁ - (i + t), by omega⟩
    have hex : e * (v₁ - i) + 1 - e * t = e * (v₁ - (i + t)) + 1 := by
      rw [show v₁ - i = t + d by omega, show v₁ - (i + t) = d by omega, mul_add]
      omega
    rw [hex]
    exact not_not.mp hn
  · have hle : e * (v₁ - i) + 1 ≤ e * t := by
      have h2 : e * (v₁ - i + 1) ≤ e * t := Nat.mul_le_mul_left e (by omega)
      rw [mul_add, mul_one] at h2
      omega
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd _

private lemma coeff_dvd_of_mem_span {O : Type} [CommRing O] (d : O) (B : ℕ) (F : PowerSeries O)
    (hF : F ∈ Ideal.span {C d, (X : PowerSeries O) ^ B}) (j : ℕ) (hj : j < B) : d ∣ coeff j F := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hF
  rw [map_add, coeff_mul_C, coeff_mul_X_pow', if_neg (by omega), add_zero]
  exact dvd_mul_left _ _

theorem content_divisibility : R2 := by
  intro O _ _ _ ϖ hϖ l hl e u he hlu f₁ a A' y B v₁ k _ hndiv hB hmem
  have hnd0 : ¬ ϖ ^ (e * v₁ + 1) ∣ coeff 0 f₁ := by
    rwa [coeff_zero_eq_constantCoeff_apply]
  obtain ⟨i₀, hi₀, hinv⟩ := exists_divisibilityInvariant ϖ e he f₁ v₁ hnd0
  have hl_dvd : ϖ ^ e ∣ (l : O) := ⟨u, by rw [hlu, mul_comm]⟩
  have hinv2 := divisibilityInvariant_mul_pow ϖ (l : O) e hl_dvd f₁ i₀ _ hinv A'
  have hF : C ((l : O) ^ a) * f₁ * (X - C (l : O)) ^ A' * X ^ y =
      (C ((l : O) ^ a) * (f₁ * (X - C (l : O)) ^ A')) * X ^ y := by ring
  have hj : i₀ + A' + y < B := by omega
  have hd := coeff_dvd_of_mem_span (ϖ ^ k) B _ hmem (i₀ + A' + y) hj
  rw [hF, coeff_mul_X_pow, coeff_C_mul] at hd

  have hnd : ¬ ϖ ^ (e * (v₁ - i₀) + 1 + e * a) ∣
      (l : O) ^ a * coeff (i₀ + A') (f₁ * (X - C (l : O)) ^ A') := by
    intro h
    apply hinv2.1
    have h' : ϖ ^ (e * a) * ϖ ^ (e * (v₁ - i₀) + 1) ∣
        ϖ ^ (e * a) * (((u ^ a : Oˣ) : O) * coeff (i₀ + A') (f₁ * (X - C (l : O)) ^ A')) := by
      rw [← pow_add, add_comm (e * a)]
      convert h using 1
      rw [hlu, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
      ring
    have h'' := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).mp h'
    exact Units.dvd_mul_left.mp h''
  have hk : k < e * (v₁ - i₀) + 1 + e * a := by
    by_contra hcon
    push_neg at hcon
    exact hnd ((pow_dvd_pow ϖ hcon).trans hd)
  have h1 : e * (v₁ - i₀) ≤ e * v₁ := Nat.mul_le_mul_left e (Nat.sub_le _ _)
  have h3 : e * (a + v₁ + 1) = e * a + e * v₁ + e := by ring
  have hk2 : k < e * (a + v₁ + 1) := by
    rw [h3]
    generalize e * (v₁ - i₀) = p at *
    generalize e * v₁ = q at *
    generalize e * a = s at *
    omega
  have he0 : (0 : ℚ) < e := by exact_mod_cast he
  rw [div_lt_iff₀ he0]
  have hq := (Nat.cast_lt (α := ℚ)).mpr hk2
  push_cast at hq
  linarith

end R2

section Kap

private lemma chi_exists (l : ℕ) [Fact l.Prime] :
    ∃ χ : ℤ_[l]ˣ, PadicInt.valuation ((χ : ℤ_[l]) - 1) = 1 := by
  have hp : 1 < l := (Fact.out : l.Prime).one_lt
  have hlt : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
  have h1 : ‖(1 + (l : ℤ_[l]))‖ = 1 := by
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left hlt.le
    · rw [norm_one, PadicInt.norm_p]
      exact hlt.ne'
  refine ⟨(PadicInt.isUnit_iff.mpr h1).unit, ?_⟩
  rw [IsUnit.unit_spec, add_sub_cancel_left, PadicInt.valuation_p]

private lemma kappa_bound_logb (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (G S h ell ro : ℕ) (a : Fin ro → ℤ)
    (JS : Finset ℤ)
    (hJS : JS ⊆ Finset.Icc (-(2 * G : ℤ)) G ∪
      Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S))
    (hD : ∀ i ∈ JS, |i| ≤ ((2 * h : ℕ) : ℤ)) :
    ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ) ≤
      (ell : ℝ) + ((3 * G + 1 + ro * S : ℕ) : ℝ) * (1 + ell) +
        (((3 * G + 1 : ℕ) : ℝ) / ((l : ℝ) - 1) + Real.logb l ((2 * h : ℕ) : ℝ) +
          ro * ((S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((2 * h : ℕ) : ℝ))) := by
  obtain ⟨χ, hχ⟩ := chi_exists l
  have hv := (Formalism.WindowSums.arc_KillerVal l hl2 χ hχ ell JS).2
  have hv' : PadicInt.valuation ((Formalism.WindowSums.PP l χ ell JS).eval 1) =
      ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) := by
    rw [hv, add_comm]
    simp_rw [add_comm 1 ell]

  have hsub : JS ⊆ Finset.univ.biUnion fun k : Fin (ro + 1) =>
      Finset.Ico ((Fin.cons (-(2 * G : ℤ)) a : Fin (ro + 1) → ℤ) k)
        ((Fin.cons (-(2 * G : ℤ)) a : Fin (ro + 1) → ℤ) k +
          ((Fin.cons (3 * G + 1) (fun _ => S) : Fin (ro + 1) → ℕ) k : ℤ)) := by
    intro i hi
    rcases Finset.mem_union.mp (hJS hi) with h1 | h2
    · rw [Finset.mem_Icc] at h1
      refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
      simp only [Fin.cons_zero, Finset.mem_Ico]
      push_cast
      omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h2
      refine Finset.mem_biUnion.mpr ⟨k.succ, Finset.mem_univ _, ?_⟩
      simpa only [Fin.cons_succ] using hk
  have hw := Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds.kappa_window_bound l hl2 χ hχ ell (ro + 1) (2 * h)
    (Fin.cons (-(2 * G : ℤ)) a) (Fin.cons (3 * G + 1) fun _ => S) JS hsub (by exact_mod_cast hD)
  rw [← hv']
  refine hw.2.trans (le_of_eq ?_)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul]
  try push_cast
  try ring

theorem killerKap_holds : KillerKap 8 := by
  intro l hl h5 G S h ell ro a hGh h1 ha JS
  have : Fact l.Prime := ⟨hl⟩
  have hl2 : l ≠ 2 := by omega
  have hD : ∀ i ∈ JS, |i| ≤ ((2 * h : ℕ) : ℤ) := by
    intro i hi
    rw [abs_le]
    push_cast
    rcases Finset.mem_union.mp hi with h2 | h2
    · rw [Finset.mem_Icc] at h2
      omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h2
      rw [Finset.mem_Ico] at hk
      have := ha k
      omega
  have hlR : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hLh : 0 ≤ Real.logb l h := Real.logb_nonneg (by linarith) hhR
  have hlog : Real.logb l ((2 * h : ℕ) : ℝ) ≤ 1 + Real.logb l h := by
    push_cast
    rw [Real.logb_mul (by norm_num) (by linarith)]
    have : Real.logb l 2 ≤ Real.logb l l :=
      Real.logb_le_logb_of_le (by linarith) (by norm_num) (by linarith)
    rw [Real.logb_self_eq_one (by linarith)] at this
    linarith
  have hdiv : ∀ x : ℝ, 0 ≤ x → x / ((l : ℝ) - 1) ≤ x := fun x hx =>
    div_le_self hx (by linarith)
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ ro := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hrS : (0 : ℝ) ≤ (ro : ℝ) * S := mul_nonneg hr0 hS0
  rcases Nat.eq_zero_or_pos S with hS | hS
  ·
    have hJS : JS ⊆ Finset.Icc (-(2 * G : ℤ)) G ∪
        Finset.univ.biUnion fun k : Fin 0 => Finset.Ico ((Fin.elim0 k : ℤ)) ((Fin.elim0 k : ℤ) + S) := by
      intro i hi
      rcases Finset.mem_union.mp hi with h2 | h2
      · exact Finset.mem_union_left _ h2
      · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h2
        rw [Finset.mem_Ico, hS] at hk
        push_cast at hk
        omega
    have hb := kappa_bound_logb l hl2 G S h ell 0 (fun k => Fin.elim0 k) JS hJS hD
    refine hb.trans ?_
    have hd1 := hdiv ((3 * G + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
    subst hS
    push_cast at hd1 hlog ⊢
    nlinarith [mul_nonneg hG0 hL0, mul_nonneg hr0 hLh]
  · have hb := kappa_bound_logb l hl2 G S h ell ro a JS (le_refl _) hD
    refine hb.trans ?_
    have hd1 := hdiv ((3 * G + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
    have hd2 := hdiv (S : ℝ) hS0
    have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have hrle : (ro : ℝ) ≤ ro * S := by nlinarith
    have h3 : (ro : ℝ) * ((S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((2 * h : ℕ) : ℝ)) ≤
        ro * (S + (1 + Real.logb l h)) := mul_le_mul_of_nonneg_left (by linarith) hr0
    push_cast at hd1 h3 hlog ⊢
    nlinarith [mul_nonneg hG0 hL0, mul_nonneg hrS hL0, mul_nonneg hr0 hLh]

end Kap

theorem content_divisibility_clause (D : Formalism.BasicNotions.D7) : adm9 D := content_divisibility

theorem killerVal_holds : Formalism.WindowSums.KillerVal := Formalism.WindowSums.arc_KillerVal

theorem killerKills_holds : Formalism.WindowSums.KillerKills := Formalism.WindowSums.arc_KillerKills

theorem killerKap_of_le {C : ℝ} (hC : 8 ≤ C) : KillerKap C := by
  intro l hl hl5 G S h ell ro a hGh hh ha
  have h8 := killerKap_holds l hl hl5 G S h ell ro a hGh hh ha
  dsimp only at h8 ⊢
  have hlog : 0 ≤ Real.logb l h :=
    Real.logb_nonneg (by exact_mod_cast (by omega : 1 < l)) (by exact_mod_cast hh)
  have hX : 0 ≤ ((G : ℝ) + ro * S + 1) * (ell + 1) + (ro + 1) * Real.logb l h :=
    add_nonneg (by positivity) (mul_nonneg (by positivity) hlog)
  exact h8.trans (mul_le_mul_of_nonneg_right hC hX)

theorem lemma_M_prime_hypothesis (D : Formalism.BasicNotions.D7) (HW : Formalism.BasicNotions.HWOf D.loc) (F : Formalism.BasicNotions.FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) (hLev : KillerLevL D.loc D.locA HW F)
    (hMod : KillerModL D.loc D.locA HW F) : adm8 D HW F C :=
  ⟨killerVal_holds, killerKills_holds, hLev, hMod, killerKap_of_le hC⟩

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section KillerBridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem γA_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = letE c := by
  funext i
  change W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

def Pi0Stable : Prop := ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u

def piNc (T : LocLat G Qp LL O) (c : ZMod n) : Submodule O (W.DD T) where
  carrier := {x | InFNc W T c W.π₀ x}
  zero_mem' := ⟨0, (W.NΔ T).zero_mem, smul_zero _, (smul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨y₁, h₁, e₁, rfl⟩ ⟨y₂, h₂, e₂, rfl⟩
    exact ⟨y₁ + y₂, (W.NΔ T).add_mem h₁ h₂, by rw [smul_add, e₁, e₂], (smul_add _ _ _).symm⟩
  smul_mem' := by
    rintro a _ ⟨y, h, e, rfl⟩
    exact ⟨a • y, (W.NΔ T).smul_mem a h, by rw [smul_comm, e], smul_comm _ _ _⟩

theorem killer_module_of_pi_stable (h : Pi0Stable W) : KillerModCore W := by
  intro _ T c ell JS w _ _ hw
  have hst : ∀ u ∈ piNc W T c, W.γ T u ∈ piNc W T c := by
    rintro _ ⟨y, hy, hc, rfl⟩
    obtain ⟨u, hu, hπ⟩ := h
    refine ⟨u • W.γD T W.gam y, ⟨(W.N T).smul_mem _ (W.N_Γ T _ y hy.1), fun δ hδ => ?_⟩, ?_, ?_⟩
    · rw [γD_smulA, hu δ hδ, ← W.γD_mul, mul_comm, W.γD_mul, hy.2 δ hδ]
    · rw [smul_comm, ← γA_letE W W.gam c, ← γD_smulA, hc]
    · change W.γD T W.gam (W.π₀ • y) = _
      rw [γD_smulA, hπ, mul_smul]
  exact Formalism.ExponentWindows.aeval_sub_eval_one_smul_mem O (W.DD T) (W.γ T) (piNc W T c) hst (PPO W ell JS) w hw

end KillerBridge

theorem killerModL_of (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT)
    (F : FonOf LT A HW)
    (h : AtCaseA fun l _ K LL hG => Pi0Stable ((HW l).W K 1 LL hG)) : KillerModL LT A HW F := by
  intro l _ K LL hG hA h5
  exact killer_module_of_pi_stable _ (h l K LL hG hA h5)

theorem pi_stability_content_clause (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) (hLev : KillerLevL D.loc D.locA HW F)
    (h : AtCaseA fun l _ K LL hG => Pi0Stable ((HW l).W K 1 LL hG)) : adm8 D HW F C :=
  lemma_M_prime_hypothesis D HW F hC hLev (killerModL_of D.loc D.locA HW F h)

end Formalism.MainNotions.ArcLiftingSetup
