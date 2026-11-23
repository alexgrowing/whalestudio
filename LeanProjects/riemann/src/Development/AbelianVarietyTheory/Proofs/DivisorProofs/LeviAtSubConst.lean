import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLogInvSqDivLeSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpAndLogPowerLeLinear

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.RegFam

open GlobalTheory.Mean4O.Deg (leviAt_add leviAt_rsmul leviAt_const smooth_const)

section Gen

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem levi_nonneg {P : LocPot X} (hp : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (w : Fin e → ℂ) : 0 ≤ leviAt A P j y w := hp _ j y ⟨hy, P.mem_U _⟩ w

theorem psh_of_levi {P : LocPot X} (hP : IsPotential A P)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ leviAt A P j y w) : IsPsh A P := by
  intro x j y hy w
  rw [GlobalTheory.LeviOnly.levi_base hP x j hy.1 hy.2]
  exact h j y hy.1 w

theorem leviAt_sub_const {g : X → ℝ} (hg : A.Smooth g) (b : ℝ) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    leviAt A (LocPot.ofFun fun x => g x - b) j y w = leviAt A (LocPot.ofFun g) j y w := by
  have h := leviAt_add A (isPotential_ofFun A _ hg) (isPotential_ofFun A _ (smooth_const A (-b))) j hy w
  rw [leviAt_const, add_zero] at h
  rw [← h]
  exact congrArg (levi · y w) (funext fun _ => sub_eq_add_neg _ _)

variable [CompactSpace X] [T2Space X]

theorem abs_levi_le {Om L : LocPot X} (hO : IsPotential A Om) (hp : IsPosPot A Om) (hL : IsPotential A L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, |leviAt A L j y w| ≤ C * leviAt A Om j y w := by
  obtain ⟨C, hC, h1, h2⟩ := ReciprocityTheory.AnForm.P.TailBoundAlt.exists_psh_chern_bound A Om L hO hp hL
  refine ⟨C, hC, fun j y hy w => ?_⟩
  have a := levi_nonneg h1 j hy w
  have b := levi_nonneg h2 j hy w
  rw [leviAt_add A (isPotentialRsmul A _ _ hO) hL j hy, leviAt_rsmul] at a
  rw [leviAt_add A (isPotentialRsmul A _ _ hO) (isPotentialRsmul A _ _ hL) j hy, leviAt_rsmul, leviAt_rsmul] at b
  rw [abs_le]
  constructor <;> linarith

theorem abs_levi_lin_le {ι : Type} [Fintype ι] {N : ℕ} {Om : LocPot X} (hO : IsPotential A Om) (hp : IsPosPot A Om)
    (th : (ι → Fin N → ℝ) → LocPot X) (hth : ∀ u, IsPotential A (th u))
    (hlin : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, IsLinearMap ℝ fun u => leviAt A (th u) j y w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u j, ∀ y ∈ (A.chart j).target, ∀ w,
      |leviAt A (th u) j y w| ≤ C * ‖u‖ * leviAt A Om j y w := by
  choose C hC h using fun p : ι × Fin N => abs_levi_le hO hp (hth (Pi.single p.1 (Pi.single p.2 1)))
  refine ⟨∑ p, C p, Finset.sum_nonneg fun p _ => hC p, fun u j y hy w => ?_⟩
  have hu : u = ∑ p : ι × Fin N, u p.1 p.2 • (Pi.single p.1 (Pi.single p.2 1) : ι → Fin N → ℝ) := by
    funext τ i
    simp [Fintype.sum_prod_type, Finset.sum_apply, Pi.single_apply, ite_apply]
  have h0 := levi_nonneg (ReciprocityTheory.AnForm.P.TailBoundAlt.isPsh_of_isPosPot A Om hp) j hy w
  have hl : leviAt A (th u) j y w =
      ∑ p : ι × Fin N, u p.1 p.2 * leviAt A (th (Pi.single p.1 (Pi.single p.2 1))) j y w := by
    have := congrArg ((hlin j y hy w).mk' _) hu
    rw [map_sum] at this
    simpa only [map_smul, IsLinearMap.mk'_apply, smul_eq_mul] using this
  rw [hl, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have h1 : |u p.1 p.2| ≤ ‖u‖ := (norm_le_pi_norm (u p.1) p.2).trans (norm_le_pi_norm u p.1)
  rw [abs_mul]
  calc _ ≤ ‖u‖ * (C p * leviAt A Om j y w) := mul_le_mul h1 (h p j y hy w) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by ring

end Gen

variable {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] {N : ℕ} {F : An M ι N}

theorem nefAn (hth : ∀ u σ, IsPotential (M.A σ) (F.th u σ)) (h : F.InS) : F.NefAn := by
  obtain ⟨s₀, hs₀, C, h⟩ := h
  intro u hu ε hε σ
  obtain ⟨s₁, hs₁, hs₁', h₁⟩ := GlobalTheory.mul_log_inv_sq_div_le_small C ‖u‖ ε hε
  have hs : 0 < min s₀ s₁ := lt_min hs₀ hs₁
  obtain ⟨hg, hp, -⟩ := h u hu _ hs (min_le_left _ _) _ rfl σ
  have h2 := h₁ _ hs (min_le_right _ _)
  have h3 : min s₀ s₁ * min (ε / 2) (1 / 4) ≤ ε := by
    have a : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
    have b : min s₀ s₁ ≤ s₁ := min_le_right _ _
    have c : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
    nlinarith
  obtain ⟨-, -, hO, hOp, -⟩ := M.bd σ
  have pF := isPotential_ofFun _ _ hg
  have pO := fun t => isPotentialRsmul _ t _ hO
  refine ⟨_, hg, psh_of_levi (isPotentialAdd _ _ _ (isPotentialAdd _ _ _ (hth u σ) (pO _)) pF) fun j y hy w => ?_⟩
  have a := levi_nonneg hp j hy w
  have h0 := levi_nonneg (ReciprocityTheory.AnForm.P.TailBoundAlt.isPsh_of_isPosPot _ _ hOp) j hy w
  rw [leviAt_add _ (isPotentialAdd _ _ _ (hth u σ) pF) (pO _) j hy, leviAt_add _ (hth u σ) pF j hy, leviAt_rsmul] at a
  rw [leviAt_add _ (isPotentialAdd _ _ _ (hth u σ) (pO _)) pF j hy, leviAt_add _ (hth u σ) (pO _) j hy, leviAt_rsmul]
  have := mul_le_mul_of_nonneg_right (h2.trans h3) h0
  linarith

theorem famS (hth : ∀ u σ, IsPotential (M.A σ) (F.th u σ)) (ha : ∀ σ, IsPotential (M.A σ) (F.a σ))
    (hlin : ∀ σ j, ∀ y ∈ ((M.A σ).chart j).target, ∀ w, IsLinearMap ℝ fun u => leviAt (M.A σ) (F.th u σ) j y w)
    (h : F.InS) {d : ι → Fin N → ℝ} (hQ : F.QPolBd d) (hS : F.Size) : F.FamS := by
  obtain ⟨s₀, hs₀, C, h⟩ := h
  obtain ⟨-, -, -, Cs, hCs⟩ := hS
  choose c hc hca using fun σ => (hQ σ).2.1
  obtain ⟨σ₀, hσ₀⟩ := Finite.exists_min c
  choose Ct hCt ht using fun σ => abs_levi_lin_le (M.bd σ).2.2.1 (M.bd σ).2.2.2.1 (fun u => F.th u σ)
    (fun u => hth u σ) (hlin σ)
  choose Ca hCa hab using fun σ => abs_levi_le (M.bd σ).2.2.1 (M.bd σ).2.2.2.1 (ha σ)
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.exp_neg_and_log_pow_div_le_mul 1
  intro Λ
  set B : ℝ := |C| * |Λ| with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨s₁, hs₁, hs₁', h₁⟩ := GlobalTheory.mul_log_inv_sq_div_le_small B 1 (c σ₀) (hc σ₀)
  have hSt : 0 ≤ (∑ σ, Ct σ) * |Λ| := mul_nonneg (Finset.sum_nonneg fun σ _ => hCt σ) (abs_nonneg _)
  have hSa : 0 ≤ ∑ σ, Ca σ := Finset.sum_nonneg fun σ _ => hCa σ
  have hSs : 0 ≤ |Cs| * |Λ| := by positivity
  have hS3 : 0 ≤ B * |C₃| := by positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∑ σ, Ct σ) * |Λ| + ∑ σ, Ca σ + |Cs| * |Λ| + 2 * B + 2 * (B * |C₃|) + 1 := ⟨_, rfl⟩
  refine ⟨min s₀ s₁, lt_min hs₀ hs₁, K, fun u hu huΛ s hs hss σ => ?_⟩
  have hs1 : s ≤ s₁ := hss.trans (min_le_right _ _)
  have hsle : s ≤ 1 := by linarith
  have huΛ' : ‖u‖ ≤ |Λ| := huΛ.trans (le_abs_self _)
  have hCB : C * ‖u‖ ≤ B := mul_le_mul (le_abs_self _) huΛ' (norm_nonneg _) (abs_nonneg _)
  obtain ⟨hg, hp, hb⟩ := h u hu s hs (hss.trans (min_le_left _ _)) _ rfl σ
  have hlog : Real.log ((s ^ 2)⁻¹) = 2 * Real.log (1 / s) := by
    rw [one_div, ← inv_pow, Real.log_pow]; norm_num
  have hl0 : 0 ≤ Real.log (1 / s) := Real.log_nonneg ((one_le_div hs).2 hsle)
  have hq0 : 0 ≤ Real.log ((s ^ 2)⁻¹) / (s ^ 2)⁻¹ := by rw [hlog]; positivity
  have hsmall : C * ‖u‖ * (Real.log ((s ^ 2)⁻¹) / (s ^ 2)⁻¹) ≤ s * c σ := by
    have a := h₁ s hs hs1
    have b := mul_le_mul_of_nonneg_right hCB hq0
    have c' : min (c σ₀ / 2) (1 / 4) ≤ c σ := (min_le_left _ _).trans (by linarith [hσ₀ σ, hc σ₀])
    have := mul_le_mul_of_nonneg_left c' hs.le
    linarith
  obtain ⟨-, -, hO, hOp, -, hr, -⟩ := M.bd σ
  have hO0 := levi_nonneg (ReciprocityTheory.AnForm.P.TailBoundAlt.isPsh_of_isPosPot _ _ hOp)
  have pF := isPotential_ofFun _ _ hg
  have pO := fun t => isPotentialRsmul _ t _ hO
  have pθ := isPotentialAdd _ _ _ (hth u σ) (isPotentialRsmul _ s _ (ha σ))
  have pP : IsPotential (M.A σ) (F.form u s (F.phS u s) σ) := isPotentialAdd _ _ _ pθ pF
  have hg' : (M.A σ).Smooth fun x => F.phS u s σ x - B := fun j => (hg j).sub contDiffOn_const
  have pF' := isPotential_ofFun _ _ hg'
  have hpsh : IsPsh (M.A σ) (F.form u s (F.phS u s) σ) := by
    refine psh_of_levi pP fun j y hy w => ?_
    have a := levi_nonneg hp j hy w
    have b := levi_nonneg (hca σ) j hy w
    rw [leviAt_add _ (isPotentialAdd _ _ _ (hth u σ) pF) (pO _) j hy, leviAt_add _ (hth u σ) pF j hy,
      leviAt_rsmul] at a
    rw [leviAt_add _ (ha σ) (pO _) j hy, leviAt_rsmul] at b
    rw [An.form, leviAt_add _ pθ pF j hy, leviAt_add _ (hth u σ) (isPotentialRsmul _ s _ (ha σ)) j hy, leviAt_rsmul]
    have c₁ := mul_le_mul_of_nonneg_right hsmall (hO0 j hy w)
    have c₂ := mul_nonneg hs.le b
    linarith
  have hθ : ∀ j, ∀ y ∈ ((M.A σ).chart j).target, ∀ w,
      |leviAt (M.A σ) (F.th u σ + (F.a σ).rsmul s) j y w| ≤ K * leviAt (M.A σ) (M.Om σ) j y w := by
    intro j y hy w
    rw [leviAt_add _ (hth u σ) (isPotentialRsmul _ s _ (ha σ)) j hy, leviAt_rsmul]
    have a : Ct σ * ‖u‖ ≤ (∑ σ, Ct σ) * |Λ| :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hCt i) (Finset.mem_univ σ)) huΛ' (norm_nonneg _)
        (Finset.sum_nonneg fun σ _ => hCt σ)
    have b : Ca σ ≤ ∑ σ, Ca σ := Finset.single_le_sum (fun i _ => hCa i) (Finset.mem_univ σ)
    have c₁ : |s * leviAt (M.A σ) (F.a σ) j y w| ≤ |leviAt (M.A σ) (F.a σ) j y w| := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_of_le_one_left (abs_nonneg _) hsle
    have c₂ : Ct σ * ‖u‖ + Ca σ ≤ K := by linarith
    have c₃ := mul_le_mul_of_nonneg_right c₂ (hO0 j hy w)
    have := ht σ u j y hy w
    have := hab σ j y hy w
    refine (abs_add_le _ _).trans ?_
    linarith
  have hEq : ∀ j, ∀ y ∈ ((M.A σ).chart j).target, ∀ w, leviAt (M.A σ) (F.form u s (F.phS u s) σ) j y w =
      leviAt (M.A σ) (F.th u σ + (F.a σ).rsmul s + LocPot.ofFun fun x => F.phS u s σ x - B) j y w := by
    intro j y hy w
    rw [An.form, leviAt_add _ pθ pF j hy, leviAt_add _ pθ pF' j hy, leviAt_sub_const hg B j hy]
  refine ⟨hg, hpsh, ⟨pP, fun _ => F.th u σ + (F.a σ).rsmul s + LocPot.ofFun fun x => F.phS u s σ x - B,
    fun _ => 1 / 3, fun _ => ⟨⟨_, _, rfl, pθ, ?_, ?_, ?_, fun x hx => ⟨?_, ?_⟩, Or.inl hg', fun j y hy _ w => ?_⟩, ?_⟩,
    fun j y hy _ w => ?_⟩, fun x => ⟨⟨?_, ?_⟩, fun hx => ⟨((hb x).2 hx).1, fun hrx => ?_⟩⟩⟩
  · refine psh_of_levi (isPotentialAdd _ _ _ (pO _) pθ) fun j y hy w => ?_
    rw [leviAt_add _ (pO _) pθ j hy, leviAt_rsmul]
    linarith [(abs_le.1 (hθ j y hy w)).1]
  · refine psh_of_levi (isPotentialAdd _ _ _ (pO _) (isPotentialRsmul _ _ _ pθ)) fun j y hy w => ?_
    rw [leviAt_add _ (pO _) (isPotentialRsmul _ _ _ pθ) j hy, leviAt_rsmul, leviAt_rsmul]
    linarith [(abs_le.1 (hθ j y hy w)).2]
  · exact fun j => (hg' j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ _)))
  · have hlr : 1 ≤ Real.log (M.r σ x) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hr x hx)
    have a := (abs_le.1 (hCs u σ x hx).1).1
    have b : Cs * ‖u‖ ≤ |Cs| * |Λ| := mul_le_mul (le_abs_self _) huΛ' (norm_nonneg _) (abs_nonneg _)
    have c₁ : Cs * ‖u‖ + B ≤ K := by linarith
    have c₂ := mul_le_mul_of_nonneg_right c₁ (zero_le_one.trans hlr)
    have c₃ := le_mul_of_one_le_right hB0 hlr
    have := ((hb x).2 hx).1
    linarith
  · linarith [(hb x).1.2]
  · rw [← hEq j y hy]
    exact levi_nonneg hpsh j hy w
  · rw [abs_of_pos (by norm_num)]
    linarith
  · rw [hEq j y hy, Fin.sum_univ_three]
    ring
  · have a := (hb x).1.1
    rw [hlog] at a
    have b : 2 * (C * ‖u‖) ≤ K := by linarith
    have c₁ := mul_le_mul_of_nonneg_right b hl0
    linarith
  · linarith [(hb x).1.2]
  · have a := ((hb x).2 hx).2.1 hrx
    obtain ⟨b₁, b₂⟩ := hC₃ s hs hsle
    rw [pow_one] at b₂
    have b₃ := mul_le_mul_of_nonneg_right (le_abs_self C₃) hs.le
    have c₁ := mul_le_mul hCB (b₁.trans b₃) (Real.exp_pos _).le hB0
    have c₂ := mul_le_mul hCB (b₂.trans b₃) hq0 hB0
    have c₃ : 2 * (B * |C₃|) ≤ K := by linarith
    have c₄ := mul_le_mul_of_nonneg_right c₃ hs.le
    linarith

theorem nefAn_and_famS : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (c : Y.Comp), (T.F c).InS → (T.F c).NefAn ∧ ∀ d, (T.F c).QPolBd d → (T.F c).Size → (T.F c).FamS := by
  intro D Y T c h
  refine ⟨nefAn (T.th_pot c) h, fun d hQ hS => famS (T.th_pot c) (T.a_pot c) (fun σ j y hy w => ⟨?_, ?_⟩) h hQ hS⟩
  · intro u v
    rw [← T.c1_L 0 c _ σ j y hy, ← T.c1_L 0 c _ σ j y hy, ← T.c1_L 0 c _ σ j y hy, map_add,
      (T.K 0 c).isOneCochain_add _ _ σ j y hy, leviAt_add _ ((T.K 0 c).firstChern_isPotential _ σ) ((T.K 0 c).firstChern_isPotential _ σ) j hy]
  · intro t u
    rw [← T.c1_L 0 c _ σ j y hy, ← T.c1_L 0 c _ σ j y hy, map_smul, (T.K 0 c).firstChern_smul_leviEq _ _ σ j y hy, leviAt_rsmul,
      smul_eq_mul]

end GlobalTheory.Mean4O.RegFam
