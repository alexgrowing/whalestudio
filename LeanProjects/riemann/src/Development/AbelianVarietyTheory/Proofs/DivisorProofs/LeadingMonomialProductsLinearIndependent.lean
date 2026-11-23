import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLE
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.JetIndepAtPts

open Topology Filter Asymptotics ReciprocityTheory.L2DbarEstimates

theorem homog_pt {n d : ℕ} (P : V n → ℂ) (hP : ∀ (t : ℂ) (y : V n), P (t • y) = t ^ d * P y)
    (h : P =O[𝓝 0] fun z => ‖z‖ ^ (d + 1)) (y : V n) : P y = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have ht : Tendsto (fun t : ℂ => t • y) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℂ => t • y) (𝓝 0) (𝓝 ((0 : ℂ) • y)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖P y‖ ≤ C * ‖y‖ ^ (d + 1) * ‖t‖ := by
    filter_upwards [ht.eventually hC, self_mem_nhdsWithin] with t h1 h2
    rw [hP, norm_mul, norm_pow, norm_smul] at h1
    rw [Real.norm_of_nonneg (by positivity), mul_pow] at h1
    have ht0 : 0 < ‖t‖ ^ d := pow_pos (norm_pos_iff.2 h2) d
    have h3 : ‖t‖ ^ d * ‖P y‖ ≤ ‖t‖ ^ d * (C * ‖y‖ ^ (d + 1) * ‖t‖) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 ht0
  have hlim : Tendsto (fun t : ℂ => C * ‖y‖ ^ (d + 1) * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℂ => C * ‖y‖ ^ (d + 1) * ‖t‖) (𝓝 0)
        (𝓝 (C * ‖y‖ ^ (d + 1) * ‖(0 : ℂ)‖)) :=
      (continuous_const.mul continuous_norm).tendsto 0
    rw [norm_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact norm_le_zero_iff.1 (ge_of_tendsto hlim hb)

theorem coeff_zero {n : ℕ} (A : Finset (Fin n → ℕ)) (b : (Fin n → ℕ) → ℂ)
    (h : ∀ y : Fin n → ℂ, ∑ α ∈ A, b α * ∏ i, y i ^ α i = 0) : ∀ α ∈ A, b α = 0 := by
  classical
  set p : MvPolynomial (Fin n) ℂ :=
    ∑ α ∈ A, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (b α) with hpdef
  have hp : p = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [hpdef, map_sum, map_zero, ← h y]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  intro α hα
  have := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α)) hp
  rw [hpdef, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  rw [Finset.sum_eq_single α] at this
  · simpa [MvPolynomial.coeff_monomial] using this
  · intro β _ hβ
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro he
    exact hβ (Finsupp.equivFunOnFinite.symm.injective he)
  · intro h'
    exact absurd hα h'

theorem homog_L {n d : ℕ} (b : (Fin n → ℕ) → ℂ) (L : V n ≃L[ℂ] V n)
    (h : (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple n d, b α * ∏ i, (L z) i ^ α i) =O[𝓝 0]
      fun z => ‖z‖ ^ (d + 1)) : ∀ α ∈ Finset.Nat.antidiagonalTuple n d, b α = 0 := by
  set P : V n → ℂ := fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple n d, b α * ∏ i, (L z) i ^ α i
    with hPdef
  have hP : ∀ (t : ℂ) (y : V n), P (t • y) = t ^ d * P y := by
    intro t y
    simp only [hPdef, map_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hs : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.1 hα
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hs]
    ring
  have h0 := homog_pt P hP h
  apply coeff_zero _ b
  intro y
  have := h0 (L.symm (WithLp.toLp 2 y))
  simpa [hPdef] using this

end GlobalTheory.JetIndepAtPts

namespace GlobalTheory.JetIndepAtPts

open Topology Filter Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

theorem expand {n δ T d : ℕ} (hd : d ≤ T) (W : V n → ℂ) (S : Fin n → V n → ℂ)
    (Tt : Fin δ → V n → ℂ) (L : V n ≃L[ℂ] V n)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0)
    (hL : ∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) (c : (Fin n → ℕ) → Fin δ → ℂ) :
    (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z -
      ∑ α ∈ Finset.Nat.antidiagonalTuple n d, (∑ k, c α k * Tt k 0 * W 0 ^ T) * ∏ i, (L z) i ^ α i)
      =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
  set φ : Fin n → V n → ℂ := fun k z => S k z / W z with hφ
  have hφa : ∀ k, AnalyticAt ℂ (φ k) 0 := fun k => (hS k).div hW hW0
  have hφ0 : ∀ k, φ k 0 = 0 := fun k => by simp [hφ, hS0]
  have hφL : ∀ k, (fun z => (L z) k - φ k z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
    intro k
    refine ((DivLA.taylor2 (hφa k)).neg_left).congr_left fun z => ?_
    rw [hφ0, hL]
    ring
  have hLO : ∀ k, (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := DivLA.comp_O L
  have hφO : ∀ k, φ k =O[𝓝 0] fun z => ‖z‖ := by
    intro k
    have h2 : (fun z => (L z) k - φ k z) =O[𝓝 0] fun z => ‖z‖ :=
      ((hφL k).trans (DivLA.isBigO_norm_pow_of_le (F := V n) (k := 1) (d := 2) (by norm_num))).congr_right
        fun z => pow_one _
    exact ((hLO k).sub h2).congr_left fun z => by ring
  have hW_ev : ∀ᶠ z in 𝓝 (0 : V n), W z ≠ 0 := hW.continuousAt.eventually_ne hW0
  set R : V n → ℂ := fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ k, c α k *
      ((Tt k 0 * W 0 ^ T - W z ^ T * Tt k z) * ∏ i, (L z) i ^ α i +
        W z ^ T * Tt k z * (∏ i, (L z) i ^ α i - ∏ i, φ i z ^ α i)) with hR
  have hRO : R =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
    refine IsBigO.fun_sum fun α hα => IsBigO.fun_sum fun k _ => (IsBigO.const_mul_left ?_ _)
    have hsα : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.1 hα
    have hg : AnalyticAt ℂ (fun z => W z ^ T * Tt k z) 0 := (hW.pow T).mul (hT k)
    have h1 : (fun z => (Tt k 0 * W 0 ^ T - W z ^ T * Tt k z) * ∏ i, (L z) i ^ α i) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      refine DivLA.mulO ((DivLA.sub_val_O hg).congr_left fun z => by ring) ?_ (by omega : 1 + d = d + 1)
      have := DivLA.prod_pow_O Finset.univ (fun i z => (L z) i) α (fun i => hLO i)
      rwa [hsα] at this
    have h2 : (fun z => W z ^ T * Tt k z * (∏ i, (L z) i ^ α i - ∏ i, φ i z ^ α i)) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      have hb : (fun z => W z ^ T * Tt k z) =O[𝓝 0] fun z => ‖z‖ ^ 0 :=
        (hg.continuousAt.tendsto.isBigO_one ℝ).congr_right fun z => (pow_zero _).symm
      have hp := DivLA.prod_pow_sub Finset.univ (fun i z => (L z) i) φ α (fun i => hLO i) hφO hφL
      rw [hsα] at hp
      exact DivLA.mulO hb hp (by omega)
    exact h1.add h2
  refine hRO.neg_left.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hW_ev] with z hz
  have hWT : W z ^ d * W z ^ (T - d) = W z ^ T := by rw [← pow_add, Nat.add_sub_cancel' hd]
  simp only [hR]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hsα : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.1 hα
  have hS' : ∀ i, S i z = W z * φ i z := fun i => by
    simp only [hφ]; field_simp
  have hprod : ∏ i, S i z ^ α i = W z ^ d * ∏ i, φ i z ^ α i := by
    simp_rw [hS', mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsα]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hprod, ← hWT]
  ring

theorem high_O {n δ d : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (Tt : Fin δ → V n → ℂ)
    (hW : AnalyticAt ℂ W 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0) (α : Fin n → ℕ) (hα : d + 1 ≤ ∑ i, α i) (c : ℂ) (e : ℕ)
    (k : Fin δ) :
    (fun z => c * (∏ i, S i z ^ α i) * W z ^ e * Tt k z) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
  have hSO : ∀ i, S i =O[𝓝 0] fun z => ‖z‖ := fun i =>
    (DivLA.sub_val_O (hS i)).neg_left.congr (fun z => by simp [hS0]) (fun z => pow_one _)
  have hp := (DivLA.prod_pow_O Finset.univ S α hSO).trans (DivLA.isBigO_norm_pow_of_le hα)
  have hb : (fun z => W z ^ e * Tt k z) =O[𝓝 0] fun z => ‖z‖ ^ 0 :=
    (((hW.pow e).mul (hT k)).continuousAt.tendsto.isBigO_one ℝ).congr_right
      fun z => (pow_zero _).symm
  exact ((DivLA.mulO hp hb (by omega)).const_mul_left c).congr_left fun z => by ring

end GlobalTheory.JetIndepAtPts

namespace GlobalTheory.JetIndepAtPts

open Topology Filter Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

theorem leadM_coeff_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (F : Fin Fl.δ → Frame X.Ψ r → ℂ), (∀ j, DifferentiableOn ℂ (F j) X.dom) → (∀ j j', F j (Fl.xs j') = if j' = j then 1 else 0) → ∀ (T : ℕ) (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ), (∀ x ∈ X.dom, leadM X Fl.s Fl.w0 F T (T + 1) cc x = 0) → ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1), ∀ k, cc α k = 0 := by
  intro E _ _ _ r X Xa Fl F hF hδ T cc h
  classical
  have key : ∀ d, d ≤ T → (∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1), ∑ q, α q < d →
      ∀ k, cc α k = 0) → ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, ∀ j, cc α j = 0 := by
    intro d hd hlow
    intro α0 hα0 j
    have hx := Fl.xs_mem j
    have hW := DivLC.anal_loc X Fl.weightForm_vanishes.1.1.1.1 hx
    have hW0 : Fl.w0 (cpt X (Fl.xs j) 0) ≠ 0 := by rw [DivLC.cpt_zero']; exact Fl.w0_ne j
    have hS := fun i => DivLC.anal_loc X (Fl.s_van i).1.1.1.1 hx
    have hS0 : ∀ i, Fl.s i (cpt X (Fl.xs j) 0) = 0 := fun i => by
      rw [DivLC.cpt_zero']; exact DivLC.s_xs_zero X Fl j i
    have hTt : ∀ k, AnalyticAt ℂ (fun z => F k (cpt X (Fl.xs j) z)) 0 :=
      fun k => DivLC.anal_loc X (hF k) hx
    obtain ⟨L, hL, -⟩ := DivLC.coordL _ _ hW hW0 hS hS0 (Fl.coord j)
    have hev : ∀ᶠ z in 𝓝 (0 : V (nd X)),
        leadM X Fl.s Fl.w0 F T (T + 1) cc (cpt X (Fl.xs j) z) = 0 := by
      have hU : IsOpen {z : V (nd X) | cpt X (Fl.xs j) z ∈ X.dom} :=
        (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).preimage (OntoB.cd_cpt X (Fl.xs j)).continuous
      filter_upwards [hU.mem_nhds (by simpa [DivLC.cpt_zero'] using hx)] with z hz
      exact h _ hz
    set f : (Fin (nd X) → ℕ) → V (nd X) → ℂ := fun α z => ∑ k, cc α k *
      (∏ i, Fl.s i (cpt X (Fl.xs j) z) ^ α i) * Fl.w0 (cpt X (Fl.xs j) z) ^ (T - ∑ q, α q) *
        F k (cpt X (Fl.xs j) z) with hfdef
    have hA : (ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1)).filter (fun α => ∑ q, α q = d) =
        Finset.Nat.antidiagonalTuple (nd X) d := by
      ext α
      simp only [Finset.mem_filter, ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
        Finset.Nat.mem_antidiagonalTuple]
      constructor
      · rintro ⟨-, h'⟩; exact h'
      · intro h'; exact ⟨⟨d, by omega, h'⟩, h'⟩
    have hsplit : ∀ z, leadM X Fl.s Fl.w0 F T (T + 1) cc (cpt X (Fl.xs j) z) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, f α z +
          ∑ α ∈ (ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1)).filter (fun α => ¬ ∑ q, α q = d), f α z := by
      intro z
      rw [← hA, Finset.sum_filter_add_sum_filter_not]
      rfl
    have hrest : (fun z => ∑ α ∈ (ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1)).filter
        (fun α => ¬ ∑ q, α q = d), f α z) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
      refine IsBigO.fun_sum fun α hα => ?_
      obtain ⟨hαm, hne⟩ := Finset.mem_filter.1 hα
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h0 : ∀ z, f α z = 0 := fun z => by
          simp [hfdef, hlow α hαm hlt]
        exact (isBigO_zero _ _).congr_left fun z => (h0 z).symm
      · exact IsBigO.fun_sum fun k _ => high_O _ _ _ hW hS hS0 hTt α hgt _ _ k
    have hH : (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, f α z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      refine hrest.neg_left.congr' ?_ (EventuallyEq.refl _ _)
      filter_upwards [hev] with z hz
      rw [hsplit] at hz
      linear_combination -hz
    have hE := expand hd (fun z => Fl.w0 (cpt X (Fl.xs j) z)) (fun i z => Fl.s i (cpt X (Fl.xs j) z))
      (fun k z => F k (cpt X (Fl.xs j) z)) L hW hW0 hS hS0 hTt hL cc
    have hf' : ∀ z, ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, f α z =
        ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d, ∑ k, cc α k *
          (∏ i, Fl.s i (cpt X (Fl.xs j) z) ^ α i) * Fl.w0 (cpt X (Fl.xs j) z) ^ (T - d) *
            F k (cpt X (Fl.xs j) z) := by
      intro z
      refine Finset.sum_congr rfl fun α hα => ?_
      simp only [hfdef, Finset.Nat.mem_antidiagonalTuple.1 hα]
    have hP : (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) d,
        (∑ k, cc α k * F k (cpt X (Fl.xs j) 0) * Fl.w0 (cpt X (Fl.xs j) 0) ^ T) *
          ∏ i, (L z) i ^ α i) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) :=
      (hH.sub hE).congr_left fun z => by rw [hf' z]; ring
    have hb := homog_L _ L hP α0 hα0
    rw [DivLC.cpt_zero'] at hb
    have hsum : ∑ k, cc α0 k * F k (Fl.xs j) * Fl.w0 (Fl.xs j) ^ T = cc α0 j * Fl.w0 (Fl.xs j) ^ T := by
      simp only [hδ]
      simp
    rw [hsum] at hb
    exact (mul_eq_zero.1 hb).resolve_right (pow_ne_zero _ (Fl.w0_ne j))
  have all : ∀ d, ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1), ∑ q, α q = d → ∀ k, cc α k = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro α hα hs k
      have hd : d ≤ T := by
        simp only [ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
          Finset.Nat.mem_antidiagonalTuple] at hα
        obtain ⟨d', hd', h'⟩ := hα
        omega
      exact key d hd (fun β hβ hlt k' => ih _ hlt β hβ rfl k') α
        (Finset.Nat.mem_antidiagonalTuple.2 hs) k
  intro α hα k
  exact all _ α hα rfl k

end GlobalTheory.JetIndepAtPts
