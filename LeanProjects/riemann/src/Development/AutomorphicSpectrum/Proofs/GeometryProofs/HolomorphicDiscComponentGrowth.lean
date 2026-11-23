import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VsReg.Chart

open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.Targets

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ratio (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : Ω := y p / y ⟨p.1, c p.1⟩

theorem hom_aeval {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (v : (Σ k, ι k) → R) (F : MRing ι) :
    φ (MvPolynomial.aeval v F) = MvPolynomial.aeval (fun p => φ (v p)) F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem aeval_eq_ratio {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {F : MRing ι}
    {d : K → ℕ} (hF : IsMultiHomog F d) :
    MvPolynomial.aeval y F = MvPolynomial.aeval (ratio y c) F * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have e : (fun p => ratio y c p * y ⟨p.1, c p.1⟩) = y := funext fun p => div_mul_cancel₀ _ (hc p.1)
  have h := FibreNormDehomRoots.aeval_scale hF (ratio y c) (fun k => y ⟨k, c k⟩)
  beta_reduce at h
  rwa [e] at h

theorem aeval_ratio_of_mem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {F : MRing ι} (hF : F ∈ mCoordIdeal y) :
    MvPolynomial.aeval (ratio y c) F = 0 := by
  have e : ratio y c = fun p => y p * (y ⟨p.1, c p.1⟩)⁻¹ := funext fun p => div_eq_mul_inv _ _
  have h := FibreNormDehomRoots.aeval_eq_zero_of_mem hF (fun k => (y ⟨k, c k⟩)⁻¹)
  beta_reduce at h
  rw [e]
  exact h

theorem aeval_ratio_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {F : MRing ι}
    (hF : Small.IsFormOff (mCoordIdeal y) F) : MvPolynomial.aeval (ratio y c) F ≠ 0 := by
  obtain ⟨⟨d, hd⟩, hn⟩ := hF
  intro h0
  apply hn
  rw [BoundedSectionTransfer.mem_mCoordIdeal_iff y hd, aeval_eq_ratio hc hd, h0, zero_mul]

theorem exists_small (C' C : ℝ) (M : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r < ρ ∧ r < 1 ∧ C' * C * r * (1 + |Real.log r|) ^ M < 1 := by
  have h1 : Tendsto (fun v : ℝ => (C' * C * Real.exp 1) * (v ^ M * Real.exp (-v))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero M).const_mul (C' * C * Real.exp 1)
  have h2 : Tendsto (fun v : ℝ => Real.exp 1 * Real.exp (-v)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp 1)
  obtain ⟨v, hv1, hv2, hv3⟩ := ((h1.eventually (Iio_mem_nhds zero_lt_one)).and
    ((h2.eventually (Iio_mem_nhds (lt_min hρ zero_lt_one))).and (eventually_gt_atTop 1))).exists
  have hr : Real.exp 1 * Real.exp (-v) = Real.exp (1 - v) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  refine ⟨Real.exp 1 * Real.exp (-v), by positivity, lt_of_lt_of_le hv2 (min_le_left _ _),
    lt_of_lt_of_le hv2 (min_le_right _ _), ?_⟩
  have hl : 1 + |Real.log (Real.exp 1 * Real.exp (-v))| = v := by
    rw [hr, Real.log_exp, abs_of_neg (by linarith)]
    ring
  rw [hl]
  calc _ = C' * C * Real.exp 1 * (v ^ M * Real.exp (-v)) := by ring
    _ < 1 := hv1

theorem one_le_of_bounds {P Q C' r B : ℝ} (hQ : 0 < Q) (hP : 0 ≤ P) (h1 : Q ≤ C' * r * P) (h2 : P / Q ≤ B) :
    1 ≤ B * C' * r := by
  have hPpos : 0 < P := by
    rcases hP.eq_or_lt with h | h
    · rw [← h, mul_zero] at h1
      linarith
    · exact h
  have hB : 0 < B := lt_of_lt_of_le (div_pos hPpos hQ) h2
  have h3 : P ≤ B * Q := (div_le_iff₀ hQ).1 h2
  have h4 : P ≤ B * (C' * r * P) := h3.trans (mul_le_mul_of_nonneg_left h1 hB.le)
  by_contra hlt
  push_neg at hlt
  have h5 : B * C' * r * P < 1 * P := mul_lt_mul_of_pos_right hlt hPpos
  have e : B * (C' * r * P) = B * C' * r * P := by ring
  linarith

section Rational

variable [Algebra ℚ Ω]

abbrev chartQ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range (ratio y c))

def gen (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : chartQ y c :=
  ⟨ratio y c p, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def ev (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (F : MRing ι) : chartQ y c :=
  MvPolynomial.aeval (gen y c) F

theorem coe_ev (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (F : MRing ι) :
    ((ev y c F : chartQ y c) : Ω) = MvPolynomial.aeval (ratio y c) F :=
  hom_aeval (algebraMap (chartQ y c) Ω) (gen y c) F

theorem chartQ_fg (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (chartQ y c).FG :=
  Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩

theorem chartQ_frac {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hBir : Birational y) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (x : Ω) : ∃ a ∈ chartQ y c, ∃ b ∈ chartQ y c, b ≠ 0 ∧ x * b = a := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hBir x
  have hT : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [aeval_eq_ratio hc hg, aeval_eq_ratio hc hh] at e
  rw [aeval_eq_ratio hc hh] at h0
  refine ⟨_, (ev y c g).2, _, (ev y c h).2, ?_, ?_⟩
  · change ((ev y c h : chartQ y c) : Ω) ≠ 0
    rw [coe_ev]
    exact left_ne_zero_of_mul h0
  · change x * ((ev y c h : chartQ y c) : Ω) = ((ev y c g : chartQ y c) : Ω)
    rw [coe_ev, coe_ev]
    apply mul_right_cancel₀ hT
    linear_combination -e

theorem exists_den {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {x : Ω} (hx : x ∈ chartQ y c) :
    ∃ N : ℕ, 0 < N ∧ (N : Ω) * x ∈ chartRingZ y c := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨1, one_pos, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin ⟨p, rfl⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have h : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      have h' := congrArg (algebraMap ℚ Ω) (Rat.den_mul_eq_num q)
      rw [map_mul, map_natCast, map_intCast] at h'
      exact h'
    rw [h]
    exact intCast_mem _ _
  | add x z _ _ hx hz =>
    obtain ⟨N₁, p₁, m₁⟩ := hx
    obtain ⟨N₂, p₂, m₂⟩ := hz
    refine ⟨N₁ * N₂, Nat.mul_pos p₁ p₂, ?_⟩
    have e : ((N₁ * N₂ : ℕ) : Ω) * (x + z) = (N₂ : Ω) * ((N₁ : Ω) * x) + (N₁ : Ω) * ((N₂ : Ω) * z) := by
      push_cast
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) m₁) (mul_mem (natCast_mem _ _) m₂)
  | mul x z _ _ hx hz =>
    obtain ⟨N₁, p₁, m₁⟩ := hx
    obtain ⟨N₂, p₂, m₂⟩ := hz
    refine ⟨N₁ * N₂, Nat.mul_pos p₁ p₂, ?_⟩
    have e : ((N₁ * N₂ : ℕ) : Ω) * (x * z) = ((N₁ : Ω) * x) * ((N₂ : Ω) * z) := by
      push_cast
      ring
    rw [e]
    exact mul_mem m₁ m₂

def DiscFor (Ω : Type) [Field Ω] [Algebra ℚ Ω] : Prop :=
  ∀ A : Subalgebra ℚ Ω, A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) →
    ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A →
      ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖

theorem mem_chartQ (hD : DiscFor Ω) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω}
    {Hb : ((Σ k, ι k) → ℂ) → ℝ} {w f₀ : MRing ι} (hBir : Birational y) (hSm : SmoothGenericFibreM y)
    (hw : Small.IsFormOff (mCoordIdeal y) w) (hf : Small.IsFormOff (mCoordIdeal y) f₀)
    (hVal : ∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z w ≠ 0 → Small.ValLe y a s z (Hb z))
    (hGrow : ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts (mCoordIdeal y)) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → MvPolynomial.aeval (Zf z) f₀ ≠ 0) →
      ∃ (C ρ : ℝ) (M : ℕ), 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Hb (Zf z) ≤ C * (1 + |Real.log ‖z‖|) ^ M)
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartQ y c := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, t = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := ⟨_, rfl⟩
  rw [← ht]
  obtain ⟨d, G, H, hG, hH, hH0, e⟩ := hBir t
  have hT : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hH1 : MvPolynomial.aeval (ratio y c) H ≠ 0 := by
    rw [aeval_eq_ratio hc hH] at hH0
    exact left_ne_zero_of_mul hH0
  have hgh : ((ev y c G : chartQ y c) : Ω) / (ev y c H : chartQ y c) = t := by
    rw [coe_ev, coe_ev, div_eq_iff hH1]
    have e' := e
    rw [aeval_eq_ratio hc hG, aeval_eq_ratio hc hH] at e'
    apply mul_right_cancel₀ hT
    linear_combination e'
  by_contra hnot
  have hb : ((ev y c w * ev y c f₀ : chartQ y c) : Ω) ≠ 0 := by
    rw [MulMemClass.coe_mul, coe_ev, coe_ev]
    exact mul_ne_zero (aeval_ratio_ne_zero hc hw) (aeval_ratio_ne_zero hc hf)
  obtain ⟨ψ, C', hol, hψ⟩ := hD (chartQ y c) (chartQ_fg y c) (hSm c hc) (chartQ_frac hBir hc)
    (ev y c G) (ev y c H) (ev y c w * ev y c f₀) (by rwa [coe_ev]) hb (by rwa [hgh])
  let Zf : ℂ → (Σ k, ι k) → ℂ := fun z p => ψ z (gen y c p)
  have hZ : ∀ z F, MvPolynomial.aeval (Zf z) F = ψ z (ev y c F) := fun z F => (hom_aeval (ψ z) (gen y c) F).symm
  have h1 : ∀ z k, Zf z ⟨k, c k⟩ = 1 := by
    intro z k
    have hg : gen y c ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    change ψ z (gen y c ⟨k, c k⟩) = 1
    rw [hg, map_one]
  have hmc : ∀ z, Zf z ∈ mcPts (mCoordIdeal y) := by
    intro z
    refine ⟨fun k => ⟨c k, by rw [h1]; exact one_ne_zero⟩, fun F hF => ?_⟩
    have h0 : ev y c F = 0 := Subtype.ext (by rw [coe_ev]; exact aeval_ratio_of_mem hF)
    have hcast : Int.castRingHom ℂ = algebraMap ℤ ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.eval_map, hcast, ← MvPolynomial.aeval_def, hZ, h0, map_zero]
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      MvPolynomial.aeval (Zf z) w ≠ 0 ∧ MvPolynomial.aeval (Zf z) f₀ ≠ 0 := by
    intro z hz hz0
    have h := (hψ z hz hz0).1
    rw [map_mul] at h
    rw [hZ, hZ]
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  obtain ⟨C, ρ, M, hρ, hgrow⟩ := hGrow Zf (fun p => hol (gen y c p)) (fun z _ => hmc z)
    (fun z hz hz0 => (hne z hz hz0).2)
  obtain ⟨r, hr0, hrρ, hr1, hsmall⟩ := exists_small C' C M hρ
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (r : ℂ) := ⟨_, rfl⟩
  have hzn : ‖z‖ = r := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hzn]; exact hr1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzn
    exact hr0.ne hzn
  obtain ⟨-, hψh, hle⟩ := hψ z hzb hz0
  have hxp : ∀ e' : K → ℕ, MvPolynomial.aeval (Zf z) (ArakelovGeometry.xpow c e') = 1 := by
    intro e'
    rw [BoundedSectionTransfer.aeval_xpow]
    exact Finset.prod_eq_one fun k _ => by rw [h1, one_pow]
  have hv : Small.HasVal y a s (Zf z) (ψ z (ev y c G) / ψ z (ev y c H)) := by
    refine ⟨d + fun k => (a k).toNat, d + fun k => (-a k).toNat, G * ArakelovGeometry.xpow c (fun k => (a k).toNat),
      H * ArakelovGeometry.xpow c (fun k => (-a k).toNat), ArakelovGeometry.isMultiHomog_mul hG (ArakelovGeometry.isMultiHomog_xpow c _),
      ArakelovGeometry.isMultiHomog_mul hH (ArakelovGeometry.isMultiHomog_xpow c _), fun k => ?_, ?_, ?_, ?_⟩
    · simp only [Pi.add_apply]
      push_cast
      omega
    · have hp : (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (a k).toNat = ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
        congr 1
        omega
      rw [map_mul, map_mul, BoundedSectionTransfer.aeval_xpow, BoundedSectionTransfer.aeval_xpow, e, ht]
      linear_combination (s * MvPolynomial.aeval y H) * hp
    · rw [map_mul, hxp, mul_one, hZ]
      exact hψh
    · rw [map_mul, map_mul, hxp, hxp, mul_one, mul_one, hZ, hZ, div_mul_cancel₀ _ hψh]
  have hb1 := hVal (Zf z) (hmc z) (hne z hzb hz0).1 _ hv
  have hb2 := hgrow z (by rw [hzn]; exact hr0) (by rw [hzn]; exact hrρ)
  rw [hzn] at hle hb2
  rw [norm_div] at hb1
  have hfin := one_le_of_bounds (norm_pos_iff.2 hψh) (norm_nonneg _) hle (hb1.trans hb2)
  have e2 : C * (1 + |Real.log r|) ^ M * C' * r = C' * C * r * (1 + |Real.log r|) ^ M := by ring
  linarith

end Rational

theorem mem_chartLatNm_of_disc : (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖) → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (Hb : ((Σ k, ι k) → ℂ) → ℝ) (w f₀ : MRing ι), Birational y → SmoothGenericFibreM y → Small.IsFormOff (mCoordIdeal y) w → Small.IsFormOff (mCoordIdeal y) f₀ → (∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z w ≠ 0 → Small.ValLe y a s z (Hb z)) → (∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → MvPolynomial.aeval (Zf z) f₀ ≠ 0) → ∃ (C ρ : ℝ) (M : ℕ), 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Hb (Zf z) ≤ C * (1 + |Real.log ‖z‖|) ^ M) → ∃ N : ℕ, 0 < N ∧ (N : Ω) * s ∈ chartLatNm y a 1 := by
  intro hDisc K _ ι _ Ω _ _ y a s Hb w f₀ hBir hSm hw hf hVal hGrow
  classical
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ N : ℕ, 0 < N ∧ (N : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ∈ chartRingZ y c :=
    fun c hc => exists_den (mem_chartQ (hDisc Ω) hBir hSm hw hf hVal hGrow hc)
  choose N hN0 hN using key
  let N' : (∀ k, ι k) → ℕ := fun c => if h : ∀ k, y ⟨k, c k⟩ ≠ 0 then N c h else 1
  have hN' : ∀ c, 0 < N' c := by
    intro c
    by_cases h : ∀ k, y ⟨k, c k⟩ ≠ 0
    · simp only [N', dif_pos h]
      exact hN0 c h
    · simp only [N', dif_neg h]
      exact one_pos
  refine ⟨∏ c, N' c, Finset.prod_pos fun c _ => hN' c, ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ : N' c ∣ ∏ c, N' c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  have hNc : N' c = N c hc := by simp only [N', dif_pos hc]
  have hmem : ((∏ c, N' c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c := by
    have e : ((∏ c, N' c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) =
        (m : Ω) * ((N c hc : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-a k))) := by
      rw [hm, hNc]
      simp only [Nat.cast_one, one_mul]
      push_cast
      ring
    rw [e]
    exact mul_mem (natCast_mem _ _) (hN c hc)
  exact isIntegral_algebraMap (R := chartRingZ y c) (x := ⟨_, hmem⟩)

end GlobalTheory.CompanionTheory.Ar.VsReg.Chart
