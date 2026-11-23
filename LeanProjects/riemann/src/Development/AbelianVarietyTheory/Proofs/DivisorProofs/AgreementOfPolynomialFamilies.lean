import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpAndLogPowerLeLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralTailBoundExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralContinuityEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIntersectionDifferenceFormulaStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.AgreePf

section One

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem cd_at {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  exact ((hf j).contDiffAt (ho.mem_nhds ⟨hy, hyU⟩)).of_le (by norm_cast)

def CdAt (A : FinHolAtlas e X) (P : LocPot X) (j : Fin A.n) (y : Fin e → ℂ) : Prop :=
  ContDiffAt ℝ 2 (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y

theorem cdAt_pot {P : LocPot X} (hP : IsPotential A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : CdAt A P j y :=
  cd_at (P.isOpen_U _) (hP.1 _) j hy (P.mem_U _)

theorem cdAt_fun {g : X → ℝ} (hg : A.Smooth g) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : CdAt A (LocPot.ofFun g) j y :=
  cd_at isOpen_univ hg j hy (Set.mem_univ _)

theorem CdAt.add {P Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : CdAt A P j y) (hQ : CdAt A Q j y) :
    CdAt A (P + Q) j y := ContDiffAt.add hP hQ

theorem CdAt.rsmul {P : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (c : ℝ) (hP : CdAt A P j y) :
    CdAt A (P.rsmul c) j y := ContDiffAt.mul contDiffAt_const hP

theorem leviAt_add {P Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (hP : CdAt A P j y) (hQ : CdAt A Q j y)
    (w : Fin e → ℂ) : leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w := by
  have h := levi_add_smul (1 : ℝ) hP hQ w
  simp only [one_mul] at h
  exact h

theorem leviAt_add_rsmul {P Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (c : ℝ) (hP : CdAt A P j y)
    (hQ : CdAt A Q j y) (w : Fin e → ℂ) :
    leviAt A (P + Q.rsmul c) j y w = leviAt A P j y w + c * leviAt A Q j y w :=
  levi_add_smul c hP hQ w

theorem leviAt_rsmul {Q : LocPot X} {j : Fin A.n} {y : Fin e → ℂ} (c : ℝ)
    (hQ : CdAt A Q j y) (w : Fin e → ℂ) :
    leviAt A (Q.rsmul c) j y w = c * leviAt A Q j y w := by
  have h1 := leviAt_add_rsmul c hQ hQ w
  have h2 := leviAt_add hQ (hQ.rsmul c) w
  linarith

theorem isPsh_mono {Om θ : LocPot X} (hO : IsPotential A Om) (hp : IsPosPot A Om)
    (hθ : ∀ x, A.SmoothOn (θ.U x) (θ.φ x)) {K K' : ℝ} (hK : K ≤ K') (h : IsPsh A (Om.rsmul K + θ)) :
    IsPsh A (Om.rsmul K' + θ) := by
  intro x j y hy w
  have h0 := h x j y hy w
  have hyO : (A.chart j).symm y ∈ Om.U x := hy.2.1
  have hyθ : (A.chart j).symm y ∈ θ.U x := hy.2.2
  have c1 := cd_at (Om.isOpen_U x) (hO.1 x) j hy.1 hyO
  have c2 := cd_at (θ.isOpen_U x) (hθ x) j hy.1 hyθ
  have c3 : ContDiffAt ℝ 2 ((Om.rsmul K + θ).φ x ∘ (A.chart j).symm) y :=
    ContDiffAt.add (ContDiffAt.mul contDiffAt_const c1) c2
  have h1 := levi_add_smul (K' - K) c3 c1 w
  have h2 : 0 ≤ levi (Om.φ x ∘ (A.chart j).symm) y w := by
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hp x j y ⟨hy.1, hyO⟩ w hw).le
  have h3 : ((Om.rsmul K' + θ).φ x ∘ (A.chart j).symm) = fun y =>
      ((Om.rsmul K + θ).φ x ∘ (A.chart j).symm) y + (K' - K) * (Om.φ x ∘ (A.chart j).symm) y := by
    funext z
    show K' * _ + _ = (K * _ + _) + (K' - K) * _
    simp only [Function.comp]
    ring
  rw [h3, h1]
  have := mul_nonneg (sub_nonneg.2 hK) h2
  linarith

variable {Z : Set X} {r : X → ℝ} {Om : LocPot X}

theorem one_le_log (hb : IsBd A Z r Om) {x : X} (hx : x ∉ Z) : 1 ≤ Real.log (r x) := by
  have h := hb.2.2.2.2.2.1 x hx
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)]
  exact h

theorem listForm_mono (hb : IsBd A Z r Om) {K K' : ℝ} (hK : K ≤ K') {T : LocPot X}
    (h : ListForm A Z r Om K T) : ListForm A Z r Om K' T := by
  obtain ⟨θ, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨θ, u, h1, h2, isPsh_mono hb.2.2.1 hb.2.2.2.1 h2.1 hK h3,
    isPsh_mono hb.2.2.1 hb.2.2.2.1 (fun x j => ContDiffOn.mul contDiffOn_const (h2.1 x j)) hK h4, h5,
    fun x hx => ⟨le_trans ?_ (h6 x hx).1, (h6 x hx).2⟩, h7, h8⟩
  have := one_le_log hb hx
  nlinarith

theorem comb_transfer (hb : IsBd A Z r Om) {K K' : ℝ} (hK : K ≤ K') {P Q : LocPot X} (hP : IsPotential A P)
    (hPQ : LeviEq A P Q) (h : Comb A Z r Om K Q) : Comb A Z r Om K' P := by
  obtain ⟨-, T, c, h1, h2⟩ := h
  exact ⟨hP, T, c, fun l => ⟨listForm_mono hb hK (h1 l).1, (h1 l).2.trans hK⟩,
    fun j y hy hz w => (hPQ j y hy w).trans (h2 j y hy hz w)⟩

end One

theorem first_chern_form_levi_sum {D : D7} {Y : ShimX D.what₂.Tau} (T : Real0 Y) (B : ℝ) (c : Y.Comp) (u : Wt Y) (s : ℝ)
    (g : (T.M c).Fun) (hg : (T.M c).Smooth g) (σ : Fin ((T.M c).n + 1)) :
    LeviEq ((T.M c).A σ) ((T.K B c).c1 (T.L B c u + s • T.a B c + (T.K B c).ar g) σ) ((T.F c).form u s g σ) := by
  intro j y hy w
  have pot := fun v => cdAt_pot ((T.K B c).firstChern_isPotential v σ) j hy
  have ht := cdAt_pot (T.th_pot c u σ) j hy
  have ha := cdAt_pot (T.a_pot c σ) j hy
  rw [(T.K B c).isOneCochain_add _ _ σ j y hy w, leviAt_add (pot _) (pot _), (T.K B c).isOneCochain_add _ _ σ j y hy w,
    leviAt_add (pot _) (pot _), (T.K B c).firstChern_smul_leviEq _ _ σ j y hy w, leviAt_rsmul _ (pot _),
    (T.K B c).c1_ar g hg σ j y hy w, T.c1_L B c u σ j y hy w, T.firstChern_leviEq_constant B c σ j y hy w]
  unfold An.form
  rw [leviAt_add (ht.add (ha.rsmul s)) (cdAt_fun (hg σ) j hy), leviAt_add_rsmul s ht ha]

theorem key {e : ℕ} (M : Man e) {ι : Type} [Fintype ι] {N : ℕ} (F : An M ι N) (j : ℕ) (hR : F.FamR j)
    (hS : F.FamS) (Λ : ℝ) : ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ (K : Calc M) (v : K.V) (u : ι → Fin N → ℝ) (s : ℝ),
      Dom u → ‖u‖ ≤ Λ → 0 < s → s ≤ s₀ →
      (∀ g, M.Smooth g → ∀ σ, LeviEq (M.A σ) (K.c1 (v + K.ar g) σ) (F.form u s g σ)) →
      M.Smooth (F.phS u s) ∧ ∀ R : ℝ, Real.exp 2 ≤ R → ((s ^ 2)⁻¹) ^ 2 ≤ R →
        |K.top (v + K.ar (F.phS u s)) - K.top (v + K.ar (F.phR R u))| ≤ C * s := by
  obtain ⟨K₁, h1⟩ := hR Λ
  obtain ⟨s₁, hs₁, K₂, h2⟩ := hS Λ
  obtain ⟨k, hk0, hk1, hk2⟩ : ∃ k : ℝ, 0 ≤ k ∧ K₁ ≤ k ∧ K₂ ≤ k :=
    ⟨max 0 (max K₁ K₂), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  choose Ct hCt using fun σ => GlobalTheory.T.mixed_integral_tail_bound_exists e (M.X σ) (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) (M.bd σ) k
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exp_and_log_power_le_linear (e + 1)
  refine ⟨min s₁ (1 / 2), lt_min hs₁ (by norm_num),
    (e + 1) * (M.κ * ∑ σ, (3 * k) ^ e * (2 * k * |Ct σ| + 3 * k * (|Ct σ| * C'))), ?_⟩
  intro K v u s hu hΛ hs hs0 hlev
  have hs1 : s ≤ s₁ := hs0.trans (min_le_left _ _)
  have hs2 : s ≤ 1 / 2 := hs0.trans (min_le_right _ _)
  have huL : DomL j u := fun τ a b hab _ => hu τ a b (by rw [Fin.le_def]; omega)
  have H2 := h2 u hu hΛ s hs hs1
  have smS : M.Smooth (F.phS u s) := fun σ => (H2 σ).1
  refine ⟨smS, fun R hR2 hRs => ?_⟩
  have H1 := h1 u huL hΛ s ⟨hs.le, by linarith⟩ R hR2
  have smR : M.Smooth (F.phR R u) := fun σ => (H1 σ).1
  set g : M.Fun := F.phS u s - F.phR R u with hg
  have smg : M.Smooth g := fun σ l => ContDiffOn.sub (smS σ l) (smR σ l)
  have hv : v + K.ar (F.phS u s) = v + K.ar (F.phR R u) + K.ar g := by
    rw [hg, map_sub]; abel
  set ℓ : ℝ := (s ^ 2)⁻¹ with hℓ
  have hℓs : ℓ * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hℓ0 : 0 < ℓ := by positivity
  have hss : s ^ 2 ≤ 1 / 4 := by nlinarith
  have hℓ4 : 4 ≤ ℓ := by nlinarith
  have hℓe : Real.exp 1 ≤ ℓ := by have := Real.exp_one_lt_d9; linarith
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 2) hR2
  have hsq : ℓ ≤ Real.sqrt R := Real.le_sqrt_of_sq_le hRs
  have hRinv : 1 / R ≤ s := by
    rw [div_le_iff₀ hR0]
    have : 1 ≤ s * ℓ := by nlinarith
    nlinarith
  have hlog : Real.log ℓ = 2 * Real.log (1 / s) := by
    rw [hℓ, one_div, ← inv_pow, Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  have hnum := (hC' s hs (by linarith)).2
  have hnum0 : 0 ≤ Real.log ℓ ^ (e + 1) / ℓ := by rw [hlog]; positivity
  have term : ∀ (i : ℕ) σ, |mInt (M.A σ) (fun l : Fin e => (if (l : ℕ) < i then
      K.c1 (v + K.ar (F.phR R u) + K.ar g) else K.c1 (v + K.ar (F.phR R u))) σ) (g σ)| ≤
      (3 * k) ^ e * (2 * k * |Ct σ| + 3 * k * (|Ct σ| * C')) * s := by
    intro i σ
    refine (GlobalTheory.T.mixed_integral_continuity_estimate e (M.X σ) (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) (M.bd σ) k (Ct σ) hk0 (hCt σ) _ (g σ)
      (2 * k * s) (3 * k) ℓ ?_ (st_smooth_continuous _ (smg σ)) (by positivity) (by positivity) hℓe ?_ ?_).trans ?_
    · intro l
      split_ifs
      · rw [← hv]
        exact comb_transfer (M.bd σ) hk2 (K.firstChern_isPotential _ σ) (hlev _ smS σ) (H2 σ).2.2.1
      · exact comb_transfer (M.bd σ) hk1 (K.firstChern_isPotential _ σ) (hlev _ smR σ) (H1 σ).2.1
    · intro x hx hr
      have a1 := ((H1 σ).2.2 x hx).2 (hr.trans hsq)
      have a2 := ((H2 σ).2.2.2 x).2 hx
      have a3 := a2.2 hr
      have a4 : K₁ / R ≤ k * s := by
        calc K₁ / R ≤ k / R := by gcongr
          _ = k * (1 / R) := by ring
          _ ≤ k * s := by gcongr
      have a5 : K₂ * s ≤ k * s := by gcongr
      have a6 := abs_le.1 (a1.trans a4)
      have a7 : 0 ≤ k * s := by positivity
      show |F.phS u s σ x - F.phR R u σ x| ≤ _
      rw [abs_le]
      constructor <;> linarith [a2.1, a6.1, a6.2]
    · intro x hx hr
      have a1 := ((H1 σ).2.2 x hx).1
      have a2 := ((H2 σ).2.2.2 x).1
      have a3 := one_le_log (M.bd σ) hx
      have a4 : Real.log ℓ ≤ Real.log (M.r σ x) := Real.log_le_log hℓ0 hr
      have a5 : K₁ * Real.log (M.r σ x) ≤ k * Real.log (M.r σ x) := by gcongr
      have a6 : K₂ * Real.log (1 / s) ≤ k * Real.log (M.r σ x) := by
        calc K₂ * Real.log (1 / s) ≤ k * Real.log (1 / s) := by gcongr
          _ ≤ k * Real.log (M.r σ x) := mul_le_mul_of_nonneg_left (by linarith) hk0
      have a7 : k ≤ k * Real.log (M.r σ x) := le_mul_of_one_le_right hk0 a3
      have a8 := abs_le.1 (a1.trans a5)
      show |F.phS u s σ x - F.phR R u σ x| ≤ _
      rw [abs_le]
      constructor <;> linarith [a2.1, a2.2, a8.1, a8.2]
    · rw [mul_assoc ((3 * k) ^ e)]
      gcongr
      have b1 : Ct σ * Real.log ℓ ^ (e + 1) / ℓ ≤ |Ct σ| * (C' * s) := by
        rw [mul_div_assoc]
        exact mul_le_mul (le_abs_self _) hnum hnum0 (abs_nonneg _)
      have b2 : 2 * k * s * Ct σ ≤ 2 * k * s * |Ct σ| := by gcongr; exact le_abs_self _
      have b3 : 3 * k * (Ct σ * Real.log ℓ ^ (e + 1) / ℓ) ≤ 3 * k * (|Ct σ| * (C' * s)) := by gcongr
      nlinarith
  rw [hv, GlobalTheory.T.top_intersection_difference_formula e M K _ g smg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _
    ((M.κ * ∑ σ, (3 * k) ^ e * (2 * k * |Ct σ| + 3 * k * (|Ct σ| * C'))) * s) fun i _ => ?_).trans ?_
  · unfold Man.int
    rw [abs_mul, abs_of_pos M.κ_pos, mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ?_ M.κ_pos.le
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => term i σ)
  · rw [Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)

theorem norm_le_supAbs {D : D7} (Y : ShimX D.what₂.Tau) (u : Wt Y) : ‖u‖ ≤ supAbs Y u := by
  have h0 : 0 ≤ supAbs Y u := Real.iSup_nonneg fun _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  exact le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)

end GlobalTheory.Mean4O.AgreePf

open GlobalTheory.Mean4O.AgreePf in

theorem GlobalTheory.Mean4O.agree_of_families (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y)
    (hR : ∀ c, (T.F c).FamR Y.j) (hS : ∀ c, (T.F c).FamS) (hP : TiePs T A) (hM : TieM T A) : Agree A := by
  intro Λ
  choose s₀ hs₀ C hC using fun c => key (T.M c) (T.F c) Y.j (hR c) (hS c) (Λ + ‖A.dir‖)
  obtain ⟨t, ht, ht1, hts⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ c, t ≤ s₀ c := by
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ c, t ≤ s₀ c :=
      Filter.eventually_all.2 fun c => nhdsWithin_le_nhds (ge_mem_nhds (hs₀ c))
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 := nhdsWithin_le_nhds (ge_mem_nhds one_pos)
    obtain ⟨t, h⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    exact ⟨t, h.2.2, h.2.1, h.1⟩
  refine ⟨t, ht, ∑ c, |C c|, fun B hB u s hu hΛ hs hst hd c => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : ‖A.sh u s‖ ≤ Λ + ‖A.dir‖ := by
    have : A.sh u s = u - (s : ℝ) • A.dir := rfl
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_le_supAbs Y u).trans hΛ) ?_)
    rw [norm_smul, Real.norm_of_nonneg hs'.le]
    exact mul_le_of_le_one_left (norm_nonneg _) (hst.trans ht1)
  have hk := fun c => hC c (T.K B c) (T.L B c (A.sh u s) + (s : ℝ) • T.a B c) (A.sh u s) s hd hn hs'
    (hst.trans (hts c)) (fun g hg σ => first_chern_form_levi_sum T B c _ _ g hg σ)
  rw [((hM B hB u s hu hs).2 hd fun c => (hk c).1).1 c]
  have hlim := ((tendsto_const_nhds (x := (T.K B c).top (T.L B c (A.sh u s) + (s : ℝ) • T.a B c +
    (T.K B c).ar ((T.F c).phS (A.sh u s) s)))).sub ((hP B hB c).2 (A.sh u s) s)).abs
  have hb := le_of_tendsto hlim (b := C c * s) (by
    filter_upwards [eventually_ge_atTop (Real.exp 2), eventually_ge_atTop ((((s : ℝ) ^ 2)⁻¹) ^ 2)] with R h1 h2
    exact (hk c).2 R h1 h2)
  refine hb.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) hs'.le)
  exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
