import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQShiftLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoordNeZero
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCount
import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaKodOf
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDiagonalSectionDifference
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite

set_option autoImplicit false

open MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsModelWithBase VeryAmple MultipleVeryAmple IsNef baseDeg pullDeg)

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

theorem tendsto_pow_div_pow {i e : ℕ} (h : i ≤ e) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ i / (n : ℝ) ^ e) atTop (𝓝 (if i = e then 1 else 0)) := by
  rcases h.eq_or_lt with rfl | hlt
  · rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [if_neg hlt.ne]
    have h0 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) ^ (e - i)) atTop (𝓝 (0 ^ (e - i))) :=
      tendsto_one_div_atTop_nhds_zero_nat.pow _
    rw [zero_pow (by omega)] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    obtain ⟨r, rfl⟩ : ∃ r, e = i + r := ⟨e - i, by omega⟩
    rw [Nat.add_sub_cancel_left, pow_add, one_div, inv_pow]
    field_simp

theorem tendsto_eval_div_pow (P : Polynomial ℚ) {e : ℕ} (hP : P.natDegree ≤ e) :
    Tendsto (fun n : ℕ => ((P.eval (n : ℚ) : ℚ) : ℝ) / (n : ℝ) ^ e) atTop (𝓝 (P.coeff e : ℝ)) := by
  have h1 : ∀ n : ℕ, ((P.eval (n : ℚ) : ℚ) : ℝ) / (n : ℝ) ^ e =
      ∑ i ∈ Finset.range (e + 1), (P.coeff i : ℝ) * ((n : ℝ) ^ i / (n : ℝ) ^ e) := by
    intro n
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Rat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  simp_rw [h1]
  have h2 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (e + 1),
      (P.coeff i : ℝ) * ((n : ℝ) ^ i / (n : ℝ) ^ e)) atTop
      (𝓝 (∑ i ∈ Finset.range (e + 1), (P.coeff i : ℝ) * (if i = e then 1 else 0))) :=
    tendsto_finset_sum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simpa [Finset.sum_ite_eq', Finset.mem_range] using h2

theorem tendsto_finrank_veryAmple {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {d : ℕ} {ν : K → ℤ}
    (hmod : IsModelWithBase F y k₀)
    (hdim : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hva : VeryAmple F y ν) :
    Tendsto (fun n : ℕ => (Module.finrank F (secOver F y (n • ν)) : ℝ) / (n : ℝ) ^ (d + 1)) atTop
      (𝓝 ((NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) / ((d + 1).factorial : ℝ))) := by
  have hpos : 0 < Fintype.card (ι k₀) := by
    obtain ⟨i, -⟩ := hmod.1 k₀
    exact Fintype.card_pos_iff.2 ⟨i⟩
  obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
  obtain ⟨Q, hQ⟩ := Kleiman.SectionsOverLocalization.BundleOfDeg.full F K ι Ω y k₀ N e hmod ν
  have hsub := (Kleiman.SectionsOverLocalization.ModelDim.proof F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
  have hvaQ := (PositivityTheory.HtPt.Ktw.a74 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
  have hnum := PositivityTheory.HtPt.Ktw.a18 F K ι Ω y k₀ N e _ rfl hmod (d + 1) (fun _ => Q) (fun _ => ν)
    (fun _ => hQ) hsub
  obtain ⟨-, P, hdeg, hc, hev⟩ := PositivityTheory.HtPt.Ktw.a37 F Ω N _ (d + 1) Q hsub hvaQ
  have hsec : ∀ n : ℕ, (Q.toSubSystem.pow n).secs = secOver F y (n • ν) := fun n => by
    have h := PositivityTheory.HtPt.Ktw.a66 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ n 0
    rw [Kleiman.twistMul, Kleiman.SubSystem.twist_twistSys_zero, zero_smul, add_zero] at h
    exact h
  have hfac : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hlim : (P.coeff (d + 1) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) / ((d + 1).factorial : ℝ) := by
    rw [eq_div_iff hfac, ← hnum]
    exact_mod_cast hc
  rw [← hlim]
  refine (tendsto_eval_div_pow P hdeg).congr' ?_
  filter_upwards [hev] with n hn
  rw [← hn, hsec n]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

theorem tendsto_div_div (p c : ℕ) (hp : 1 ≤ p) :
    Tendsto (fun τ : ℕ => ((τ / p + c : ℕ) : ℝ) / (τ : ℝ)) atTop (𝓝 (1 / (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : Tendsto (fun τ : ℕ => 1 / (p : ℝ) + (c : ℝ) * (1 / (τ : ℝ))) atTop (𝓝 (1 / (p : ℝ))) := by
    simpa using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c : ℝ)).const_add (1 / (p : ℝ))
  have h2 : Tendsto (fun τ : ℕ => 1 / (p : ℝ) - 1 / (τ : ℝ)) atTop (𝓝 (1 / (p : ℝ))) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub (1 / (p : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with τ hτ
    have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
    have hlt : τ < (τ / p + 1) * p := by
      have h := Nat.div_add_mod τ p
      have h' := Nat.mod_lt τ (by omega : p > 0)
      nlinarith
    have hlt' : (τ : ℝ) ≤ (((τ / p : ℕ) : ℝ) + 1) * p := by exact_mod_cast hlt.le
    have h3 : (τ : ℝ) / p ≤ ((τ / p : ℕ) : ℝ) + 1 := (div_le_iff₀ hp0).2 hlt'
    have e : 1 / (p : ℝ) - 1 / (τ : ℝ) = ((τ : ℝ) / p - 1) / τ := by field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hτ0.le
    push_cast
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  · filter_upwards [eventually_gt_atTop 0] with τ hτ
    have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
    have h3 : ((τ / p : ℕ) : ℝ) ≤ (τ : ℝ) / p := Nat.cast_div_le
    have e : 1 / (p : ℝ) + (c : ℝ) * (1 / (τ : ℝ)) = ((τ : ℝ) / p + c) / τ := by field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hτ0.le
    push_cast
    linarith

theorem tendsto_div_add (p c : ℕ) (hp : 1 ≤ p) : Tendsto (fun τ : ℕ => τ / p + c) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b * p)] with τ hτ
  have := (Nat.le_div_iff_mul_le (by omega : 0 < p)).2 hτ
  omega

theorem eventually_le_of_growth {D : ℕ} {f u : ℕ → ℝ} {X : ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hu : Tendsto (fun n : ℕ => u n / (n : ℝ) ^ D) atTop (𝓝 X))
    (hle : ∀ᶠ τ : ℕ in atTop, f τ ≤ u (τ / p + 1)) :
    ∀ ε > 0, ∀ᶠ τ : ℕ in atTop, f τ / (τ : ℝ) ^ D ≤ X / (p : ℝ) ^ D + ε := by
  intro ε hε
  have h1 := (hu.comp (tendsto_div_add p 1 hp)).mul ((tendsto_div_div p 1 hp).pow D)
  have hX : X * (1 / (p : ℝ)) ^ D = X / (p : ℝ) ^ D := by
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [hX] at h1
  filter_upwards [h1.eventually_lt_const (lt_add_of_pos_right _ hε), hle, eventually_gt_atTop 0]
    with τ h2 h3 hτ
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hn0 : (0 : ℝ) < ((τ / p + 1 : ℕ) : ℝ) := by positivity
  have e : (Function.comp (fun n : ℕ => u n / (n : ℝ) ^ D) fun τ : ℕ => τ / p + 1) τ *
      (((τ / p + 1 : ℕ) : ℝ) / (τ : ℝ)) ^ D = u (τ / p + 1) / (τ : ℝ) ^ D := by
    simp only [Function.comp, div_pow]
    field_simp
  have h2' : u (τ / p + 1) / (τ : ℝ) ^ D < X / (p : ℝ) ^ D + ε := by
    rw [← e]
    exact h2
  exact (div_le_div_of_nonneg_right h3 (by positivity)).trans h2'.le

theorem eventually_ge_of_growth {d : ℕ} {f v : ℕ → ℝ} {X C C₁ : ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hv : ∀ n : ℕ, 1 ≤ n → X * (n : ℝ) ^ (d + 1) - C * (n : ℝ) ^ d ≤ v n)
    (hle : ∀ᶠ τ : ℕ in atTop, v (τ / p) ≤ f τ + C₁ * (τ : ℝ) ^ d) :
    ∀ ε > 0, ∀ᶠ τ : ℕ in atTop, X / (p : ℝ) ^ (d + 1) - ε ≤ f τ / (τ : ℝ) ^ (d + 1) := by
  intro ε hε
  have hr : Tendsto (fun τ : ℕ => ((τ / p : ℕ) : ℝ) / (τ : ℝ)) atTop (𝓝 (1 / (p : ℝ))) := by
    simpa using tendsto_div_div p 0 hp
  have hz : Tendsto (fun τ : ℕ => 1 / (τ : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun τ : ℕ => X * (((τ / p : ℕ) : ℝ) / (τ : ℝ)) ^ (d + 1) -
      C * ((((τ / p : ℕ) : ℝ) / (τ : ℝ)) ^ d * (1 / (τ : ℝ))) - C₁ * (1 / (τ : ℝ))) atTop
      (𝓝 (X * (1 / (p : ℝ)) ^ (d + 1) - C * ((1 / (p : ℝ)) ^ d * 0) - C₁ * 0)) :=
    (((hr.pow _).const_mul X).sub (((hr.pow _).mul hz).const_mul C)).sub (hz.const_mul C₁)
  have hX : X * (1 / (p : ℝ)) ^ (d + 1) - C * ((1 / (p : ℝ)) ^ d * 0) - C₁ * 0 =
      X / (p : ℝ) ^ (d + 1) := by
    rw [one_div, inv_pow, div_eq_mul_inv]
    ring
  rw [hX] at h1
  filter_upwards [h1.eventually_const_lt (sub_lt_self _ hε), hle, tendsto_div_add p 0 hp
    |>.eventually (eventually_ge_atTop 1), eventually_gt_atTop 0] with τ h2 h3 h4 hτ
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  have h5 := hv (τ / p) (by simpa using h4)
  have e : X * (((τ / p : ℕ) : ℝ) / (τ : ℝ)) ^ (d + 1) -
      C * ((((τ / p : ℕ) : ℝ) / (τ : ℝ)) ^ d * (1 / (τ : ℝ))) - C₁ * (1 / (τ : ℝ)) =
      (X * ((τ / p : ℕ) : ℝ) ^ (d + 1) - C * ((τ / p : ℕ) : ℝ) ^ d - C₁ * (τ : ℝ) ^ d) /
        (τ : ℝ) ^ (d + 1) := by
    have ht : (τ : ℝ) ^ (d + 1) = (τ : ℝ) ^ d * τ := pow_succ _ _
    simp only [div_pow]
    rw [ht]
    field_simp
  rw [e] at h2
  refine h2.le.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  linarith

theorem tendsto_of_bounds {g Φ Ψ : ℕ → ℝ} {G : ℝ} (hΦ : Tendsto Φ atTop (𝓝 G)) (hΨ : Tendsto Ψ atTop (𝓝 0))
    (hU : ∀ q : ℕ, 1 ≤ q → ∀ ε > 0, ∀ᶠ τ : ℕ in atTop, g τ ≤ Φ q + ε)
    (hL : ∀ q : ℕ, 1 ≤ q → ∀ ε > 0, ∀ᶠ τ : ℕ in atTop, Φ q - Ψ q - ε ≤ g τ) :
    Tendsto g atTop (𝓝 G) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hm : a + (G - a) / 3 < G := by linarith
    have hs : Tendsto (fun q => Φ q - Ψ q) atTop (𝓝 G) := by simpa using hΦ.sub hΨ
    obtain ⟨q, hq, h1⟩ := ((eventually_ge_atTop 1).and (hs.eventually_const_lt hm)).exists
    filter_upwards [hL q hq ((G - a) / 3) (by linarith)] with τ hτ
    linarith
  · have hm : G < b - (b - G) / 3 := by linarith
    obtain ⟨q, hq, h1⟩ := ((eventually_ge_atTop 1).and (hΦ.eventually_lt_const hm)).exists
    filter_upwards [hU q hq ((b - G) / 3) (by linarith)] with τ hτ
    linarith

theorem tendsto_multilinear {M : Type} [AddCommGroup M] {n : ℕ}
    (g : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (β e : M) :
    Tendsto (fun q : ℕ => (g (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ n) atTop
      (𝓝 (g (fun _ => β) : ℝ)) := by
  classical
  have h1 : ∀ q : ℕ, g (fun _ => (q : ℤ) • β + e) = ∑ s : Finset (Fin n),
      (q : ℤ) ^ s.card * g (s.piecewise (fun _ => β) (fun _ => e)) := by
    intro q
    have h := g.map_add_univ (fun _ => (q : ℤ) • β) (fun _ => e)
    refine h.trans (Finset.sum_congr rfl fun s _ => ?_)
    have h2 := g.map_piecewise_smul (fun _ => (q : ℤ)) (s.piecewise (fun _ => β) (fun _ => e)) s
    have e2 : s.piecewise (fun _ => (q : ℤ) • β) (fun _ => e) =
        s.piecewise (fun i => (q : ℤ) • s.piecewise (fun _ => β) (fun _ => e) i)
          (s.piecewise (fun _ => β) (fun _ => e)) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [e2, h2, Finset.prod_const, smul_eq_mul]
  have h3 : ∀ q : ℕ, (g (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ n = ∑ s : Finset (Fin n),
      (g (s.piecewise (fun _ => β) (fun _ => e)) : ℝ) * ((q : ℝ) ^ s.card / (q : ℝ) ^ n) := by
    intro q
    rw [h1 q]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [h3]
  have h4 : Tendsto (fun q : ℕ => ∑ s : Finset (Fin n),
      (g (s.piecewise (fun _ => β) (fun _ => e)) : ℝ) * ((q : ℝ) ^ s.card / (q : ℝ) ^ n)) atTop
      (𝓝 (∑ s : Finset (Fin n), (g (s.piecewise (fun _ => β) (fun _ => e)) : ℝ) *
        (if s.card = n then 1 else 0))) :=
    tendsto_finset_sum _ fun s _ => (tendsto_pow_div_pow (by
      simpa using s.card_le_univ)).const_mul _
  convert h4 using 2
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro s _ hs
    have : s.card ≠ n := fun h => hs (by
      apply Finset.eq_univ_of_card
      simpa using h)
    simp [this]
  · simp

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

section Sections

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mul_monomial_mem_secOver (y : (Σ k, ι k) → Ω) (j : ∀ k, ι k) (e : K → ℕ) {b : K → ℤ} {s : Ω}
    (hs : s ∈ secOver F y b) :
    s * ∏ k, y ⟨k, j k⟩ ^ e k ∈ secOver F y (b + fun k => (e k : ℤ)) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule] at hs ⊢
  intro c hc
  have h1 := hs c hc
  have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingOver F y c :=
    fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ e k ∈ chartRingOver F y c :=
    prod_mem fun k _ => pow_mem (hq k) _
  have heq : s * (∏ k, y ⟨k, j k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ (-(b + fun k => (e k : ℤ) : K → ℤ) k) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) * ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ e k := by
    rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have hck := hc k
    have hz : y ⟨k, c k⟩ ^ (-(b + fun k => (e k : ℤ) : K → ℤ) k) =
        y ⟨k, c k⟩ ^ (-b k) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
      congr 1
      simp only [Pi.add_apply]
      ring
    rw [hz, div_pow, div_eq_mul_inv]
    ring
  rw [heq]
  exact mul_mem h1 h2

theorem finrank_secOver_mono {y : (Σ k, ι k) → Ω} (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {b b' : K → ℤ}
    (hb : ∀ k, b k ≤ b' k) (hfd : FiniteDimensional F (secOver F y b')) :
    Module.finrank F (secOver F y b) ≤ Module.finrank F (secOver F y b') := by
  choose j hj using hnz
  set e : K → ℕ := fun k => (b' k - b k).toNat with he
  have hb' : b + (fun k => (e k : ℤ)) = b' := by
    funext k
    simp only [Pi.add_apply, he]
    have := hb k
    omega
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ secOver F y b, s * ∏ k, y ⟨k, j k⟩ ^ e k ∈ secOver F y b' := fun s hs => by
    have := mul_monomial_mem_secOver y j e hs
    rwa [hb'] at this
  let f : secOver F y b →ₗ[F] secOver F y b' :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ e k, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end Sections

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

section Growth

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω]

theorem smul_pull_add (a : K → ℤ) (n p m : ℕ) :
    n • ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K)) =
      pullDeg ((((n * p : ℕ) : ℤ)) • a) + (((n * m : ℕ) : ℤ)) • baseDeg (Sum.inl () : Unit ⊕ K) := by
  funext k
  cases k with
  | inl u => simp [pullDeg, baseDeg, Pi.single_apply]
  | inr k =>
    simp [pullDeg, baseDeg, Pi.single_apply]
    ring

theorem secOver_segre (y : (Σ k, ι k) → Ω) (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (a : K → ℤ) (n p m : ℕ) :
    secOver F (Kleiman.SectionsOverLocalization.segreJoin y)
        (n • ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K))) =
      secOver F y ((((n * p : ℕ) : ℤ)) • a + fun _ => (((n * m : ℕ) : ℤ))) := by
  rw [smul_pull_add]
  exact Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz _ _

end Growth

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

section Main

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω]

theorem smul_add_nonneg {a A r p n : ℤ} (ha : -A ≤ a) (hA : 0 ≤ A) (hr : 0 ≤ r) (hrp : r ≤ p) (hn : p * A ≤ n) :
    0 ≤ r * a + n := by
  nlinarith [mul_nonneg hr (by linarith : 0 ≤ a + A), mul_nonneg (by linarith : 0 ≤ p - r) hA]

theorem upper_of_veryAmple {y : (Σ k, ι k) → Ω} (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {d : ℕ} {a : K → ℤ}
    (hd : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hfd : ∀ b, FiniteDimensional F (secOver F y b)) {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hva : VeryAmple F (Kleiman.SectionsOverLocalization.segreJoin y)
      ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K))) :
    ∀ ε > 0, ∀ᶠ τ : ℕ in atTop,
      (Module.finrank F (secOver F y ((τ : ℤ) • a)) : ℝ) / (τ : ℝ) ^ (d + 1) ≤
        (NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
            (fun _ : Fin (d + 1) => (p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K)) : ℝ) /
          ((d + 1).factorial : ℝ) / (p : ℝ) ^ (d + 1) + ε := by
  have hmod := (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
  have hdim := (Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hd
  have hu := tendsto_finrank_veryAmple hmod hdim hva
  refine eventually_le_of_growth hp hu ?_
  set A : ℤ := ∑ k, |a k| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hak : ∀ k, -A ≤ a k := fun k =>
    (neg_le_neg (Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k))).trans (neg_abs_le _)
  filter_upwards [eventually_ge_atTop (p * p * A.toNat)] with τ hτ
  rw [secOver_segre y hnz a]
  have hfin := hfd ((((τ / p + 1) * p : ℕ) : ℤ) • a + fun _ => ((((τ / p + 1) * m : ℕ)) : ℤ))
  refine Nat.cast_le.2 (finrank_secOver_mono hnz (fun k => ?_) hfin)
  have hdiv := Nat.div_add_mod τ p
  have hlt := Nat.mod_lt τ (by omega : p > 0)
  set t := τ / p with ht
  have htA : p * A.toNat ≤ t := (Nat.le_div_iff_mul_le (by omega)).2 (by
    rw [show p * A.toNat * p = p * p * A.toNat by ring]
    exact hτ)
  have hAn : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
  have h1 : (τ : ℤ) = p * t + ((τ % p : ℕ) : ℤ) := by exact_mod_cast hdiv.symm
  have h2 : ((τ % p : ℕ) : ℤ) < p := by exact_mod_cast hlt
  have h3 : (0 : ℤ) ≤ ((τ % p : ℕ) : ℤ) := Int.natCast_nonneg _
  have e1 : (((t + 1) * p : ℕ) : ℤ) = p * t + p := by push_cast; ring
  have h4 : (p : ℤ) * A ≤ (((t + 1) * m : ℕ) : ℤ) := by
    have h5 : t ≤ (t + 1) * m := by nlinarith
    have h6 : p * A.toNat ≤ (t + 1) * m := htA.trans h5
    rw [← hAn]
    exact_mod_cast h6
  have key := smul_add_nonneg (a := a k) (A := A) (r := (((t + 1) * p : ℕ) : ℤ) - τ) (p := p)
    (n := (((t + 1) * m : ℕ) : ℤ)) (hak k) hA0 (by rw [e1, h1]; linarith) (by rw [e1, h1]; linarith) h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e2 : ((((t + 1) * p : ℕ) : ℤ) - τ) * a k = (((t + 1) * p : ℕ) : ℤ) * a k - τ * a k := by ring
  linarith

theorem lower_of_veryAmple (hS : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement)
    {y : (Σ k, ι k) → Ω} (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {d : ℕ} {a : K → ℤ}
    (hd : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hfd : ∀ b, FiniteDimensional F (secOver F y b))
    (hsh : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank F (secOver F y ((n : ℤ) • a + fun _ => (M : ℤ))) : ℝ) ≤
        (Module.finrank F (secOver F y ((n : ℤ) • a)) : ℝ) + C * (n : ℝ) ^ d)
    {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hva : VeryAmple F (Kleiman.SectionsOverLocalization.segreJoin y)
      ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K))) :
    ∀ ε > 0, ∀ᶠ τ : ℕ in atTop,
      (((NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
            (fun _ : Fin (d + 1) => (p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K)) : ℝ) -
          ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
            (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ) (fun _ : Fin d =>
                (p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K))
              (m • baseDeg (Sum.inl () : Unit ⊕ K))) : ℝ)) / ((d + 1).factorial : ℝ)) / (p : ℝ) ^ (d + 1) - ε ≤
        (Module.finrank F (secOver F y ((τ : ℤ) • a)) : ℝ) / (τ : ℝ) ^ (d + 1) := by
  have hmod := (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
  have hdim := (Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hd
  obtain ⟨C, hC⟩ := hS F _ _ Ω (Kleiman.SectionsOverLocalization.segreJoin y) (Sum.inl ()) d _ m hmod hdim hva hm
  set A : ℤ := ∑ k, |a k| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hak : ∀ k, -A ≤ a k := fun k =>
    (neg_le_neg (Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ k))).trans (neg_abs_le _)
  obtain ⟨C₁, hC₁⟩ := hsh (p * A.toNat)
  refine eventually_ge_of_growth (C := C) (C₁ := C₁)
    (v := fun n : ℕ => (Module.finrank F (secOver F (Kleiman.SectionsOverLocalization.segreJoin y) (n •
      ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K) -
        m • baseDeg (Sum.inl () : Unit ⊕ K)))) : ℝ)) hp (fun n hn => ?_) ?_
  · have h := hC n hn
    rw [div_mul_eq_mul_div]
    exact h
  · filter_upwards [hC₁] with τ hτ
    have hsec : ∀ n : ℕ, secOver F (Kleiman.SectionsOverLocalization.segreJoin y) (n •
        ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K) -
          m • baseDeg (Sum.inl () : Unit ⊕ K))) = secOver F y (((n * p : ℕ) : ℤ) • a) := by
      intro n
      have e0 : n • ((p • pullDeg (K₁ := Unit) a) + (m : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K) -
          m • baseDeg (Sum.inl () : Unit ⊕ K)) =
          pullDeg (((n * p : ℕ) : ℤ) • a) + (0 : ℤ) • baseDeg (Sum.inl () : Unit ⊕ K) := by
        funext k
        cases k with
        | inl u => simp [pullDeg, baseDeg, Pi.single_apply]
        | inr k =>
          simp [pullDeg, baseDeg, Pi.single_apply]
          ring
      rw [e0, Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz]
      congr 1
      funext k
      simp
    beta_reduce
    rw [hsec]
    refine le_trans (Nat.cast_le.2 (finrank_secOver_mono hnz (fun k => ?_) (hfd _))) hτ
    have hdiv := Nat.div_add_mod τ p
    have hlt := Nat.mod_lt τ (by omega : p > 0)
    set t := τ / p with ht
    have hAn : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
    have h1 : (τ : ℤ) = p * t + ((τ % p : ℕ) : ℤ) := by exact_mod_cast hdiv.symm
    have h2 : ((τ % p : ℕ) : ℤ) < p := by exact_mod_cast hlt
    have h3 : (0 : ℤ) ≤ ((τ % p : ℕ) : ℤ) := Int.natCast_nonneg _
    have e1 : ((t * p : ℕ) : ℤ) = p * t := by push_cast; ring
    have key := smul_add_nonneg (a := a k) (A := A) (r := ((τ % p : ℕ) : ℤ)) (p := p)
      (n := ((p * A.toNat : ℕ) : ℤ)) (hak k) hA0 h3 h2.le (by push_cast; rw [hAn])
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, h1]
    nlinarith

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

section Nef

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω]

def fixLast {M : Type} [AddCommGroup M] {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (e : M) :
    MultilinearMap ℤ (fun _ : Fin d => M) ℤ :=
  (LinearMap.applyₗ e).compMultilinearMap (f.curryRight)

theorem tendsto_finrank_nef (hK : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement)
    (hS : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement)
    {y : (Σ k, ι k) → Ω} (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {d : ℕ} {a : K → ℤ}
    (hd : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef F y a)
    (hfd : ∀ b, FiniteDimensional F (secOver F y b))
    (hsh : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank F (secOver F y ((n : ℤ) • a + fun _ => (M : ℤ))) : ℝ) ≤
        (Module.finrank F (secOver F y ((n : ℤ) • a)) : ℝ) + C * (n : ℝ) ^ d) :
    Tendsto (fun τ : ℕ => (Module.finrank F (secOver F y ((τ : ℤ) • a)) : ℝ) / (τ : ℝ) ^ (d + 1)) atTop
      (𝓝 ((NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => a) : ℝ) / ((d + 1).factorial : ℝ))) := by
  have hmod := (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
  have hdim := (Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hd
  have hnef' := (Kleiman.SectionsOverLocalization.SegreNef.proof Kleiman.SectionsOverLocalization.SegreDim.proof Kleiman.SectionsOverLocalization.SegreNum.proof
    F K ι Ω y hnz a).2 hnef
  have hP := Kleiman.SectionsOverLocalization.isMultiProjPrime_mIdealOver (S := F) (Kleiman.SectionsOverLocalization.segreJoin y) hmod.1
  obtain ⟨f, hf⟩ := PositivityTheory.HtPt.Siub.exists_multilinear (M := Unit ⊕ K → ℤ) (n := d + 1)
    (fun v => NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y)) v)
    (FieldNumbers.IntNumAdd.full F (Unit ⊕ K) _ (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y)) hP.multiHomog
      hP.relevant (d + 1) hdim)
  set β : Unit ⊕ K → ℤ := pullDeg (K₁ := Unit) a with hβ
  set e : Unit ⊕ K → ℤ := baseDeg (Sum.inl () : Unit ⊕ K) with he
  have hG : NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => a) = f (fun _ => β) := by
    rw [hf]
    exact (Kleiman.SectionsOverLocalization.SegreNum.proof F K ι Ω y hnz (d + 1) (fun _ => a)).symm
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hΦ : Tendsto (fun q : ℕ => (f (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ (d + 1) /
      ((d + 1).factorial : ℝ)) atTop (𝓝 ((f (fun _ => β) : ℝ) / ((d + 1).factorial : ℝ))) :=
    (tendsto_multilinear f β e).div_const _
  have hΨ : Tendsto (fun q : ℕ => ((d + 1 : ℕ) : ℝ) * ((fixLast f e (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ d *
      (1 / (q : ℝ))) / ((d + 1).factorial : ℝ)) atTop (𝓝 0) := by
    have h := (((tendsto_multilinear (fixLast f e) β e).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).const_mul ((d + 1 : ℕ) : ℝ)).div_const
        ((d + 1).factorial : ℝ)
    simpa using h
  have key : ∀ q : ℕ, 1 ≤ q → ∃ p m : ℕ, 1 ≤ p ∧ 1 ≤ m ∧ p = q * m ∧
      VeryAmple F (Kleiman.SectionsOverLocalization.segreJoin y) ((p • β) + (m : ℤ) • e) := by
    intro q hq
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq
    obtain ⟨p, m, hp, hm, hva⟩ := hK (d + 1) F _ _ Ω (Kleiman.SectionsOverLocalization.segreJoin y) (Sum.inl ()) hmod hdim β
      hnef' (1 / (q : ℚ)) (by positivity)
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp
    have hmpos : 0 < m := by
      have : (0 : ℚ) < m := by rw [hm]; positivity
      exact_mod_cast this
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
    have hr : 1 ≤ r := by exact_mod_cast hmpos
    have hpq : p = q * r := by
      have h1 : (r : ℚ) * q = p := by
        have h2 : ((r : ℤ) : ℚ) = p * (1 / (q : ℚ)) := hm
        push_cast at h2
        rw [h2]
        field_simp
      have h3 : r * q = p := by exact_mod_cast h1
      rw [← h3, mul_comm]
    exact ⟨p, r, hp, hr, hpq, hva⟩
  rw [hG]
  have hν : ∀ {p m q : ℕ}, p = q * m → (p • β) + (m : ℤ) • e = (m : ℤ) • ((q : ℤ) • β + e) := by
    intro p m q hpq
    subst hpq
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hF : ∀ {p m q : ℕ}, p = q * m → f (fun _ => (p • β) + (m : ℤ) • e) =
      (m : ℤ) ^ (d + 1) * f (fun _ => (q : ℤ) • β + e) := by
    intro p m q hpq
    have h := f.map_smul_univ (fun _ => (m : ℤ)) (fun _ => (q : ℤ) • β + e)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    rw [hν hpq]
    exact h
  have hX : ∀ {p m q : ℕ}, 1 ≤ q → 1 ≤ m → p = q * m →
      (NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
        (fun _ : Fin (d + 1) => (p • β) + (m : ℤ) • e) : ℝ) / ((d + 1).factorial : ℝ) / (p : ℝ) ^ (d + 1) =
      (f (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
    intro p m q hq hm hpq
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hf0 := hfac.ne'
    rw [← hf (fun _ => (p • β) + (m : ℤ) • e), hF hpq, hpq]
    push_cast
    rw [mul_pow]
    field_simp
  refine tendsto_of_bounds hΦ hΨ (fun q hq ε hε => ?_) (fun q hq ε hε => ?_)
  · obtain ⟨p, m, hp, hm, hpq, hva⟩ := key q hq
    refine (upper_of_veryAmple hnz hd hfd hp hm hva ε hε).mono fun τ hτ => hτ.trans_eq ?_
    exact congrArg (· + ε) (hX hq hm hpq)
  · obtain ⟨p, m, hp, hm, hpq, hva⟩ := key q hq
    have hs : Fin.snoc (α := fun _ => Unit ⊕ K → ℤ) (fun _ : Fin d => (p • β) + (m : ℤ) • e) (m • e) =
        fun i => (m : ℤ) • (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ)
          (fun _ : Fin d => (q : ℤ) • β + e) e : Fin (d + 1) → Unit ⊕ K → ℤ) i := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, natCast_zsmul]
      · simp only [Fin.snoc_castSucc, hν hpq]
    have hS1 : f (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ) (fun _ : Fin d => (p • β) + (m : ℤ) • e) (m • e)) =
        (m : ℤ) ^ (d + 1) * fixLast f e (fun _ => (q : ℤ) • β + e) := by
      have h := f.map_smul_univ (fun _ => (m : ℤ))
        (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ) (fun _ : Fin d => (q : ℤ) • β + e) e)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
      rw [hs]
      exact h
    have hY : (((NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
            (fun _ : Fin (d + 1) => (p • β) + (m : ℤ) • e) : ℝ) -
          ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F (Kleiman.SectionsOverLocalization.segreJoin y))
            (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ) (fun _ : Fin d => (p • β) + (m : ℤ) • e) (m • e)) : ℝ)) /
            ((d + 1).factorial : ℝ)) / (p : ℝ) ^ (d + 1) =
        (f (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
          ((d + 1 : ℕ) : ℝ) * ((fixLast f e (fun _ => (q : ℤ) • β + e) : ℝ) / (q : ℝ) ^ d * (1 / (q : ℝ))) /
            ((d + 1).factorial : ℝ) := by
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hf0 := hfac.ne'
      rw [← hf (fun _ => (p • β) + (m : ℤ) • e), ← hf (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ)
        (fun _ : Fin d => (p • β) + (m : ℤ) • e) (m • e)), hF hpq, hS1, hpq]
      have hqd : (q : ℝ) ^ (d + 1) = (q : ℝ) ^ d * q := pow_succ _ _
      push_cast
      rw [mul_pow, hqd]
      field_simp
    refine (lower_of_veryAmple hS hnz hd hfd hsh hp hm hva ε hε).mono fun τ hτ => le_trans (le_of_eq ?_) hτ
    exact (congrArg (· - ε) hY).symm

end Nef

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

section Final

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_secOver (y : (Σ k, ι k) → Ω) (b : K → ℤ) : chartLatQ y b 1 = secOver ℚ y b := by
  ext s
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  have h3 : ∀ (c : ∀ k, ι k) (j : K), -(((1 : ℕ) : ℤ) * b j) = -b j := fun _ j => by simp
  constructor
  · intro h c hc
    have h1 := h c hc
    simp only [h3 c] at h1
    exact h1
  · intro h c hc
    have h1 := h c hc
    show s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) ∈ chartRingQ y c
    simp only [h3 c]
    exact h1

theorem chartLatQ_smul (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y ((τ : ℤ) • a) 1 = chartLatQ y a τ := by
  ext s
  have h3 : ∀ j, -(((1 : ℕ) : ℤ) * ((τ : ℤ) • a) j) = -((τ : ℤ) * a j) := fun j => by simp
  change (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((τ : ℤ) • a) k)) ∈ chartRingQ y c) ↔
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingQ y c)
  simp only [h3]

theorem shiftSectionBound : ShiftSectionBound.Statement :=
  have hL : SectionLatticeFinite.Statement := SectionLatticeFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond
  ShiftSectionBound.proof hL (ShiftQuotientBound.proof hL
    (HyperplaneQuotientBound.proof HyperplaneRegularSection.full DiagonalSectionDifference.proof hL)
    HyperplaneRegularSection.full)

theorem tendsto_div_of_squeeze {f g : ℕ → ℝ} {L C : ℝ} {d : ℕ}
    (hf : Tendsto (fun τ : ℕ => f τ / (τ : ℝ) ^ (d + 1)) atTop (𝓝 L))
    (h1 : ∀ τ, f τ ≤ g τ) (h2 : ∀ᶠ τ : ℕ in atTop, g τ ≤ f τ + C * (τ : ℝ) ^ d) :
    Tendsto (fun τ : ℕ => g τ / (τ : ℝ) ^ (d + 1)) atTop (𝓝 L) := by
  have hz : Tendsto (fun τ : ℕ => f τ / (τ : ℝ) ^ (d + 1) + C * (1 / (τ : ℝ))) atTop (𝓝 L) := by
    simpa using hf.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hz ?_ ?_
  · exact Eventually.of_forall fun τ => div_le_div_of_nonneg_right (h1 τ) (by positivity)
  · filter_upwards [h2, eventually_gt_atTop 0] with τ hτ hpos
    have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hpos
    have e : f τ / (τ : ℝ) ^ (d + 1) + C * (1 / (τ : ℝ)) =
        (f τ + C * (τ : ℝ) ^ d) / (τ : ℝ) ^ (d + 1) := by
      rw [pow_succ]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hτ (by positivity)

end Final

theorem nefRR_succ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (hV : IsArithVar (mCoordIdeal y) (d + 1 + 1))
    (hB : Birational y) (hN : NefOnGenericDeg (mCoordIdeal y) a) :
    (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))) ∧
      Tendsto (fun τ : ℕ => ((d + 1).factorial : ℝ) *
        (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ (d + 1)) atTop
        (𝓝 (genDeg (mCoordIdeal y) (d + 1) a : ℝ)) := by
  classical
  obtain ⟨hK, hS⟩ := (GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput).2
  have : Nonempty K := hV.1
  have hI : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz := GlobalTheory.CompanionTheory.Ar.Relevant.exists_coord_ne_zero K ι Ω y (d + 1) hV
  have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  have hfinQ : ∀ b, FiniteDimensional ℚ (chartLatQ y b 1) := fun b =>
    GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) b hV
  have hfd : ∀ b, FiniteDimensional ℚ (secOver ℚ y b) := fun b => by
    rw [← chartLatQ_eq_secOver]
    exact hfinQ b
  have hsh : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a + fun _ => (M : ℤ))) : ℝ) ≤
        (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a)) : ℝ) + C * (n : ℝ) ^ d := by
    intro M
    obtain ⟨C, hC⟩ := shiftSectionBound K ι Ω y (d + 1) a M (by omega) hV hB
    refine ⟨C, hC.mono fun n hn => ?_⟩
    have h := hn.2
    rw [Nat.add_sub_cancel, chartLatQ_eq_secOver, chartLatQ_eq_secOver] at h
    exact h
  have hlim := tendsto_finrank_nef hK hS hnz hdim hnef hfd hsh
  obtain ⟨e, c, hc0, hcond⟩ := GlobalTheory.CompanionTheory.Conductor.exists_conductor_section K ι Ω y (d + 1) hV hB

  let φ : ∀ τ : ℕ, Submodule.span ℚ (chartLatNm y a τ : Set Ω) →ₗ[ℚ]
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := fun τ =>
    { toFun := fun s => ⟨c * s.1, hcond a τ s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm _ _ _) }
  have hφ : ∀ τ, Function.Injective (φ τ) := fun τ s t hst =>
    Subtype.ext (mul_left_cancel₀ hc0 (congrArg Subtype.val hst))
  have hfinS : ∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := fun τ => by
    have := hfinQ ((τ : ℤ) • a + fun k => (e k : ℤ))
    exact FiniteDimensional.of_injective (φ τ) (hφ τ)
  refine ⟨hfinS, ?_⟩
  set M : ℕ := ∑ k, e k with hM
  have heM : ∀ k, e k ≤ M := fun k => Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨C, hC⟩ := hsh M
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (secOver ℚ y ((τ : ℤ) • a + fun _ => (M : ℤ))) := fun τ => by
    have h1 : Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
        Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
      have := hfinQ ((τ : ℤ) • a + fun k => (e k : ℤ))
      exact LinearMap.finrank_le_finrank_of_injective (hφ τ)
    have h2 := GlobalTheory.CompanionTheory.ChartSections.finrank_chartLatQ_shift_le K ι Ω y ((τ : ℤ) • a) e M hnz heM (hfinQ _)
    rw [← chartLatQ_eq_secOver]
    exact h1.trans h2
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (secOver ℚ y ((τ : ℤ) • a)) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := fun τ => by
    have := hfinS τ
    rw [← chartLatQ_eq_secOver, chartLatQ_smul]
    exact Submodule.finrank_mono (GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm K ι Ω y a τ)
  have hg := tendsto_div_of_squeeze (C := C) (g := fun τ : ℕ =>
      (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) hlim
    (fun τ => Nat.cast_le.2 (hlow τ))
    (hC.mono fun τ hτ => le_trans (Nat.cast_le.2 (hup τ)) hτ)
  have hfac : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hgen : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) =
      ((d + 1).factorial : ℝ) * ((NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) : ℝ) /
        ((d + 1).factorial : ℝ)) := by
    rw [mul_div_cancel₀ _ hfac, ← hI]
    rfl
  rw [hgen]
  simp only [mul_div_assoc]
  exact hg.const_mul _

end GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  cases D with
  | zero => exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  | succ d => exact NefVolume.nefRR_succ y d a hV hB hN

end GlobalTheory.CompanionTheory.Hypotheses₂
