import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolarStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearFormsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutationStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PResAboveCover

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.RootNum

def rc {N : ℕ} (i k : Fin N) : ℤ := (if (k : ℕ) + 1 = i then 1 else 0) - (if k = i then 1 else 0)

theorem sum_rc_smul {N : ℕ} {A : Type} [AddCommGroup A] (a : Fin N → A) (i : Fin N) :
    ∑ k : Fin N, rc i k • (-∑ l ∈ Finset.Iic k, a l) = a i := by
  have h1 : ∀ k : Fin N, rc i k • (-∑ l ∈ Finset.Iic k, a l) =
      (if (k : ℕ) + 1 = i then (-∑ l ∈ Finset.Iic k, a l) else 0) -
        (if k = i then (-∑ l ∈ Finset.Iic k, a l) else 0) := by
    intro k
    unfold rc
    split_ifs <;> simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    have h2 : Finset.Iic (⟨0, hi⟩ : Fin N) = {⟨0, hi⟩} := by
      ext l
      simp [Fin.ext_iff, Fin.le_def]
    simp [h2]
  | succ j =>
    have hj : j < N := by omega
    have h3 : ∑ k : Fin N, (if (k : ℕ) + 1 = j + 1 then (-∑ l ∈ Finset.Iic k, a l) else 0) =
        -∑ l ∈ Finset.Iic (⟨j, hj⟩ : Fin N), a l := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (by simpa using h))
      · simp
    have h4 : Finset.Iic (⟨j + 1, hi⟩ : Fin N) = insert ⟨j + 1, hi⟩ (Finset.Iic ⟨j, hj⟩) := by
      ext l
      simp [Fin.ext_iff, Fin.le_def]
      omega
    simp only [h3]
    rw [h4, Finset.sum_insert (by simp [Fin.le_def])]
    abel

theorem sum_mul_rc {N : ℕ} (l : Fin N → ℝ) (k : Fin N) :
    ∑ i : Fin N, l i * (rc i k : ℝ) = (if h : (k : ℕ) + 1 < N then l ⟨k + 1, h⟩ else 0) - l k := by
  have h1 : ∀ i : Fin N, l i * (rc i k : ℝ) =
      (if (k : ℕ) + 1 = i then l i else 0) - (if k = i then l i else 0) := by
    intro i
    unfold rc
    split_ifs <;> simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k + 1, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro e
    exact h (e ▸ b.2)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def rootC : Option (Ψ × Fin N) → Option (Ψ × Fin N) → ℤ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some p, some q => if q.1 = p.1 then rc p.2 q.2 else 0

theorem sum_rootC_none {A : Type} [AddCommGroup A] (g : Option (Ψ × Fin N) → A) :
    ∑ b, rootC none b • g b = g none := by
  simp [Fintype.sum_option, rootC]

theorem sum_rootC_some {A : Type} [AddCommGroup A] (g : Option (Ψ × Fin N) → A) (a : Ψ × Fin N → A)
    (hg : ∀ τ k, g (some (τ, k)) = -∑ l ∈ Finset.Iic k, a (τ, l)) (p : Ψ × Fin N) :
    ∑ b, rootC (some p) b • g b = a p := by
  rw [Fintype.sum_option]
  simp only [rootC, zero_smul, zero_add]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
  · simp only [if_true, hg]
    exact sum_rc_smul (fun l => a (p.1, l)) p.2
  · intro b _ hb
    simp [hb]
  · simp

theorem sum_coef_rootC (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (b : Option (Ψ × Fin N)) :
    ∑ o, M.coef lam s o * (rootC o b : ℝ) = PB.gapS (fun x => lam x.1 x.2) (s / M.kA) b := by
  rw [Fintype.sum_option]
  cases b with
  | none => simp [rootC, RootModel.coef, PB.gapS]
  | some q =>
    simp only [rootC, RootModel.coef, Int.cast_zero, mul_zero, zero_add]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q.1]
    · simp only [if_true, mul_comm, neg_mul]
      have := sum_mul_rc (fun i => lam q.1 i) q.2
      simp only [PB.gapS, Option.elim, PB.gap, PB.gapX]
      rw [Finset.sum_neg_distrib, this]
      by_cases h : (q.2 : ℕ) + 1 < N <;> simp [h]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp

section Lines

variable {M : RootModel Ψ N} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ}

theorem line_none_h (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) (z : (Σ k, M.ι k) → ℂ)
    (hz : z ∈ mcPts M.P) : (R.Re.line none t).h z = M.A.h z := by
  obtain ⟨x, c, hc, hzx⟩ := GroundTheory.Heights₂.Heights.Targets.ResAboveCover.surj_all
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full M.P R.Re.J R.Re.R R.Re.arith z hz
  have hum : R.Re.R.lift x x ∈ mcPts M.P := R.Re.R.mem x x (R.Re.R.mem_U x)
  have e := R.Re.line_eq none t ht0 ht x
  rw [R.phT_none, add_zero] at e
  have e' : (R.Re.line none t).h (R.Re.R.lift x x) = (R.Re.ref none).h (R.Re.R.lift x x) :=
    Real.log_injOn_pos (Set.mem_Ioi.2 ((R.Re.line none t).pos _ hum.1))
      (Set.mem_Ioi.2 ((R.Re.ref none).pos _ hum.1)) e
  rw [← R.ref_none.2 z hz, hzx, (R.Re.line none t).smul c _ hc, (R.Re.ref none).smul c _ hc, e',
    R.Re.line_deg]

theorem comb_a (R : RealTie M S n) (t : ℝ) (o : Option (Ψ × Fin N)) :
    (PB.combLine (fun b => R.Re.line b t) (rootC o)).a = (M.line t o).a := by
  funext κ
  rw [PB.combLine_a]
  simp only [← smul_eq_mul]
  cases o with
  | none =>
    rw [sum_rootC_none (fun b => (R.Re.line b t).a κ), R.Re.line_deg, R.ref_none.1]
    rfl
  | some p =>
    rw [sum_rootC_some (fun b => (R.Re.line b t).a κ) (fun q => M.xdeg q κ)]
    · show _ = (M.x t p).a κ
      rw [M.x_deg]
    · intro τ k
      rw [R.Re.line_deg, R.fund_deg]
      simp [Finset.sum_apply]

theorem comb_h (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) (o : Option (Ψ × Fin N))
    (z : (Σ k, M.ι k) → ℂ) (hz : z ∈ mcPts M.P) :
    (PB.combLine (fun b => R.Re.line b t) (rootC o)).h z = (M.line t o).h z := by
  have hp : ∀ b, 0 < (R.Re.line b t).h z := fun b => (R.Re.line b t).pos z hz.1
  have hlog : Real.log ((PB.combLine (fun b => R.Re.line b t) (rootC o)).h z) =
      ∑ b, rootC o b • Real.log ((R.Re.line b t).h z) := by
    rw [PB.combLine_h, Real.log_prod (fun b _ => (zpow_pos (hp b) _).ne')]
    simp [Real.log_zpow]
  refine Real.log_injOn_pos (Set.mem_Ioi.2 ((PB.combLine (fun b => R.Re.line b t) (rootC o)).pos z hz.1))
    (Set.mem_Ioi.2 ((M.line t o).pos z hz.1)) ?_
  rw [hlog]
  cases o with
  | none =>
    rw [sum_rootC_none (fun b => Real.log ((R.Re.line b t).h z)), line_none_h R t ht0 ht z hz]
    rfl
  | some p =>
    rw [sum_rootC_some (fun b => Real.log ((R.Re.line b t).h z)) (fun q => Real.log ((M.x t q).h z))]
    · rfl
    · intro τ k
      exact R.fund_reg τ k t ht0 ht z hz

theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (o : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t o) := by
  cases o with
  | none => exact M.A_smooth
  | some p => exact M.x_smooth t p

theorem word_eq (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀)
    (w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N)) :
    II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r)) =
      PB.polar (dimFl Ψ N + 1) (fun v => II M.K M.ι M.P (dimFl Ψ N + 1) fun r => R.Re.line (v r) t)
        (fun r a => (rootC (w r) a : ℝ)) := by
  have hc := GlobalTheory.T.arithmetic_intersection_multilinear_polar hL II hII M.K M.ι (Option (Ψ × Fin N)) M.P (dimFl Ψ N + 1)
    (fun a => R.Re.line a t) (fun r => rootC (w r)) R.Re.arith (fun a => R.Re.line_smooth a t ht0 ht)
  rw [← hc.2]
  exact hL M.K M.ι (II M.K M.ι) (hII.1 M.K M.ι) M.P _ _ _ R.Re.arith (fun j => smooth_line M t _) hc.1
    (fun j => (comb_a R t _).symm) (fun j z hz => (comb_h R t ht0 ht _ z hz).symm)

end Lines

theorem eval_formPoly {σ : Type} [Fintype σ] (d : ℕ) (a : (Fin d → σ) → ℝ) (c : σ → ℝ) :
    eval c (PB.formPoly d a) = ∑ w, a w * ∏ j, c (w j) := by
  simp [PB.formPoly, map_sum, map_prod]

theorem polar_swap {J : Type} [Fintype J] [DecidableEq J] {d : ℕ} (c : J → ℝ) (nn : J → J → ℝ)
    (I : (Fin d → J) → ℝ) :
    ∑ w : Fin d → J, (∏ k, c (w k)) * PB.polar d I (fun r a => nn (w r) a) =
      ∑ v : Fin d → J, (∏ r, ∑ o, c o * nn o (v r)) * I v := by
  simp only [PB.polar, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

def cS (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ := fun o => o.elim s fun r => -lam r.1 r.2

theorem linA_eq (lam : Wt Ψ N) (s : ℝ) : linA lam s = ∑ j, C (cS lam s j) * X j := by
  rw [Fintype.sum_option]
  simp [linA, toA, linRoot, cS, map_sum, add_comm]

variable (M : RootModel Ψ N) (II : IntersectionSystem)

theorem arFun_monomial (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.arFun II t (monomial m 1) = M.arMono II t m := by
  have := (basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ (M.arMono II t) m
  simpa [RootModel.arFun] using this

theorem PP_monomial (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  have := (basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ
    (fun m => limUnder (𝓝[>] (0 : ℝ)) fun t => M.arMono II t m) m
  simpa [RootModel.PP] using this

theorem prod_cS (lam : Wt Ψ N) (s : ℝ) {d : ℕ} (w : Fin d → Option (Ψ × Fin N)) :
    ∏ k, cS lam s (w k) = (∏ k, M.coef lam s (w k)) *
      (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) := by
  have hk : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.kA_pos.ne'
  rw [Finsupp.finset_sum_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  cases w k with
  | none => simp [cS, RootModel.coef, hk]
  | some r => simp [cS, RootModel.coef]

theorem arFun_lin (hII : IsFullIntersectionSystem II) (lam : Wt Ψ N) (s t : ℝ) :
    M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) =
      (∑ w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N), (∏ k, M.coef lam s (w k)) *
        II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r))) / M.δ := by
  have hk : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.kA_pos.ne'
  have hd : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  have e : linA lam s ^ (dimFl Ψ N + 1) =
      ∏ _k : Fin (dimFl Ψ N + 1), ∑ j, C (cS lam s j) * X j := by
    rw [linA_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e]
  have h1 := GlobalTheory.T.functional_product_linear_forms (Option (Ψ × Fin N)) (dimFl Ψ N + 1) (M.arFun II t)
    (fun _ => cS lam s)
  rw [h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hdeg, σ, -, hii⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 M.K M.ι M.P (dimFl Ψ N + 1)
    (Option (Ψ × Fin N)) (M.line t) w M.arith (smooth_line M t)
  rw [arFun_monomial, RootModel.arMono, if_pos hdeg, hii, prod_cS M lam s w]
  have hp : ((M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none)) ≠ 0 :=
    pow_ne_zero _ hk
  field_simp

theorem exists_word {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (m : J →₀ ℕ) {d : ℕ}
    (hm : m.degree = d) : ∃ w : Fin d → J, ∀ ℓ : J → HermLine ι, monoLines ℓ m d = fun k => ℓ (w k) := by
  have hlen : (Finsupp.toMultiset m).toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hm]
    simp only [Finsupp.sum, id]
    rfl
  refine ⟨fun k => (Finsupp.toMultiset m).toList.get ⟨k, by omega⟩, fun ℓ => funext fun k => ?_⟩
  simp only [monoLines]
  rw [dif_pos (by omega)]

section Limits

variable {M II} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ}

theorem num_eq (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) (hII : IsFullIntersectionSystem II)
    (R : RealTie M S n) (lam : Wt Ψ N) (s t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) :
    (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) =
      eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t) := by
  have hdeg : (R.Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 R.Re.deg_pos.ne'
  have hδ : (M.δ : ℝ) = n * R.Re.deg := by exact_mod_cast R.δ_eq
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    have h' : (M.δ : ℝ) = 0 := by rw [hδ, h, zero_mul]
    exact (Nat.cast_ne_zero.2 M.δ_pos.ne') h'
  have e : ∑ w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N), (∏ k, M.coef lam s (w k)) *
        II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r)) =
      ∑ v : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N),
        (∏ r, PB.gapS (fun x => lam x.1 x.2) (s / M.kA) (v r)) *
          II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => R.Re.line (v r) t) := by
    simp only [word_eq hL II hII R t ht0 ht]
    refine (polar_swap (M.coef lam s) (fun o a => (rootC o a : ℝ)) _).trans ?_
    simp only [sum_coef_rootC]
  rw [arFun_lin M II hII, PB.Realis.FT, eval_formPoly, e, hδ, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [PB.Realis.num]
  field_simp

theorem exists_lim_arMono (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (hII : IsFullIntersectionSystem II) (R : RealTie M S n)
    (hconv : ∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w)))
    (h0 : 0 < S.t₀) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ∃ L, Tendsto (fun t => M.arMono II t m) (𝓝[>] 0) (𝓝 L) := by
  by_cases hm : m.degree = dimFl Ψ N + 1
  · obtain ⟨w, hw⟩ := exists_word (ι := M.ι) m hm
    have hdeg : (R.Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 R.Re.deg_pos.ne'
    have h1 : Tendsto (fun t => PB.polar (dimFl Ψ N + 1) (fun v => (R.Re.deg : ℝ) * R.Re.num II t v)
          (fun r a => (rootC (w r) a : ℝ)) / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none)) (𝓝[>] 0)
        (𝓝 (PB.polar (dimFl Ψ N + 1) (fun v => (R.Re.deg : ℝ) * R.Re.limNum II v)
          (fun r a => (rootC (w r) a : ℝ)) / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))) := by
      refine Tendsto.div_const ?_ _
      simp only [PB.polar]
      exact tendsto_finset_sum _ fun v _ => ((hconv v).const_mul _).const_mul _
    refine ⟨_, h1.congr' ?_⟩
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    have e : (fun v => (R.Re.deg : ℝ) * R.Re.num II t v) =
        fun v => II M.K M.ι M.P (dimFl Ψ N + 1) fun r => R.Re.line (v r) t := by
      funext v
      rw [PB.Realis.num]
      field_simp
    rw [RootModel.arMono, if_pos hm, hw, word_eq hL II hII R t ht.1 ht.2, e]
  · refine ⟨0, ?_⟩
    simp only [RootModel.arMono, if_neg hm]
    exact tendsto_const_nhds

theorem tendsto_arFun (hC : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have e : monomial u a = a • (monomial u (1 : ℝ) : RPA Ψ N) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    obtain ⟨L, hLim⟩ := hC u
    simp only [e, map_smul, arFun_monomial, PP_monomial, smul_eq_mul]
    rw [hLim.limUnder_eq]
    exact hLim.const_mul a
  | add p q hp hq => simpa only [map_add] using hp.add hq

end Limits

theorem arith_degrees : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), 0 < n ∧ (∀ t, 0 < t → t ≤ S.t₀ → (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) ∧ ((∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w))) → 0 < S.t₀ → M.Converges II ∧ (n : ℝ) * M.PP II (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II)) := by
  intro hI II hII Ψ _ _ N M S n R lam s
  have hL := hI.metricLocal
  refine ⟨Nat.pos_of_ne_zero fun h => M.δ_pos.ne' (R.δ_eq.trans (Nat.mul_eq_zero.2 (Or.inl h))),
    fun t ht0 ht => num_eq hL hII R lam s t ht0 ht, fun hconv h0 => ?_⟩
  have hC : M.Converges II := exists_lim_arMono hL hII R hconv h0
  refine ⟨hC, ?_⟩
  have h1 := (tendsto_arFun hC (linA lam s ^ (dimFl Ψ N + 1))).const_mul (n : ℝ)
  have h2 : Tendsto (fun t => eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) (𝓝[>] 0)
      (𝓝 (eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II))) := by
    simp only [PB.Realis.FT, PB.Realis.PB, eval_formPoly]
    exact tendsto_finset_sum _ fun v _ => (hconv v).mul_const _
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [Ioc_mem_nhdsGT h0] with t ht
  exact num_eq hL hII R lam s t ht.1 ht.2

end GlobalTheory.CompanionTheory.Ar.Top.RootNum
