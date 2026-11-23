import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermLineOfLocalSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace Flat

open GlobalTheory.CompanionTheory.Ar.LocVal

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_eval (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    aeval z f = eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_map, aeval_def]
  rfl

theorem mem_ptsOver {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P :=
  ⟨hz.1, fun f hf => by rw [aeval_eq_eval]; exact hz.2 f hf⟩

theorem analytic_aeval (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    AnalyticAt ℂ (fun z : (Σ k, ι k) → ℂ => aeval z f) z := by
  simp only [aeval_eq_eval]
  exact AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)

def Rep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (ks : K) (d : ι ks × MRing ι × MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog d.2.1 dg ∧ IsMultiHomog d.2.2 dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y d.2.1 = y ⟨ks, d.1⟩ * aeval y d.2.2

def NZ {ks : K} (d : ι ks × MRing ι × MRing ι) (z : (Σ k, ι k) → ℂ) : Prop :=
  z ⟨ks, d.1⟩ ≠ 0 ∧ aeval z d.2.1 ≠ 0 ∧ aeval z d.2.2 ≠ 0

def rho {ks : K} (d : ι ks × MRing ι × MRing ι) (z : (Σ k, ι k) → ℂ) : ℂ :=
  z ⟨ks, d.1⟩ * aeval z d.2.2 / aeval z d.2.1

theorem rho_ne {ks : K} {d : ι ks × MRing ι × MRing ι} {z : (Σ k, ι k) → ℂ} (h : NZ d z) : rho d z ≠ 0 :=
  div_ne_zero (mul_ne_zero h.1 h.2.2) h.2.1

theorem isOpen_NZ {ks : K} (d : ι ks × MRing ι × MRing ι) : IsOpen {z | NZ d z} := by
  have c1 : Continuous fun z : (Σ k, ι k) → ℂ => aeval z d.2.1 :=
    continuous_iff_continuousAt.2 fun z => (analytic_aeval _ z).continuousAt
  have c2 : Continuous fun z : (Σ k, ι k) → ℂ => aeval z d.2.2 :=
    continuous_iff_continuousAt.2 fun z => (analytic_aeval _ z).continuousAt
  exact (isOpen_ne_fun (continuous_apply _) continuous_const).inter
    ((isOpen_ne_fun c1 continuous_const).inter (isOpen_ne_fun c2 continuous_const))

theorem analytic_rho {ks : K} {d : ι ks × MRing ι × MRing ι} {z : (Σ k, ι k) → ℂ} (h : NZ d z) :
    AnalyticAt ℂ (rho d) z := by
  have a0 : AnalyticAt ℂ (fun z : (Σ k, ι k) → ℂ => z ⟨ks, d.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, ι k => ℂ) ⟨ks, d.1⟩).analyticAt z
  exact (a0.mul (analytic_aeval _ z)).div (analytic_aeval _ z) h.2.1

theorem rho_eq {y : (Σ k, ι k) → Ω} {a : K → ℤ} {ks : K} {d d' : ι ks × MRing ι × MRing ι}
    (h : Rep y a ks d) (h' : Rep y a ks d') {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (n : NZ d z) (n' : NZ d' z) : rho d z = rho d' z := by
  obtain ⟨dg, dh, hg, hh, hd, e⟩ := h
  obtain ⟨dg', dh', hg', hh', hd', e'⟩ := h'
  have h1 := homog_mul (homog_mul (homog_X ks d.1) hh) hg'
  have h2 := homog_neg (homog_mul (homog_mul (homog_X ks d'.1) hh') hg)
  have h3 := homog_add h1 (by
    convert h2 using 1
    funext k
    have a1 := hd k
    have a2 := hd' k
    simp only [Pi.add_apply]
    omega)
  have h4 := aeval_eq_zero_of (mem_ptsOver hz) h3 (by
    simp only [map_add, map_neg, map_mul, aeval_X, e, e']
    ring)
  simp only [map_add, map_neg, map_mul, aeval_X] at h4
  unfold rho
  rw [div_eq_div_iff n.2.1 n'.2.1]
  linear_combination h4

theorem NZ_smul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {ks : K} {d : ι ks × MRing ι × MRing ι}
    (h : Rep y a ks d) {z : (Σ k, ι k) → ℂ} (n : NZ d z) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    NZ d (fun p => c p.1 * z p) ∧ Real.log ‖rho d (fun p => c p.1 * z p)‖ =
      Real.log ‖rho d z‖ + ∑ k, (((Pi.single ks 1 - a : K → ℤ) k : ℤ) : ℝ) * Real.log ‖c k‖ := by
  obtain ⟨dg, dh, hg, hh, hd, e⟩ := h
  have p1 : (∏ k, c k ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have p2 : (∏ k, c k ^ dh k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have e1 := aeval_scale hg c z
  have e2 := aeval_scale hh c z
  refine ⟨⟨mul_ne_zero (hc _) n.1, by rw [e1]; exact mul_ne_zero p1 n.2.1, by rw [e2]; exact mul_ne_zero p2 n.2.2⟩, ?_⟩
  have e3 : rho d (fun p => c p.1 * z p) = rho d z * (c ks * (∏ k, c k ^ dh k) / ∏ k, c k ^ dg k) := by
    unfold rho
    rw [e1, e2]
    have := n.2.1
    field_simp
  have hl : ∀ w : K → ℕ, Real.log ‖∏ k, c k ^ w k‖ = ∑ k, (w k : ℝ) * Real.log ‖c k‖ := fun w => by
    rw [norm_prod, Real.log_prod (fun k _ => norm_ne_zero_iff.2 (pow_ne_zero _ (hc k)))]
    simp only [norm_pow, Real.log_pow]
  rw [e3, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (rho_ne n))
    (norm_ne_zero_iff.2 (div_ne_zero (mul_ne_zero (hc _) p2) p1)), norm_div, norm_mul,
    Real.log_div (mul_ne_zero (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 p2)) (norm_ne_zero_iff.2 p1),
    Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 p2), hl, hl]
  congr 1
  have e4 : ∀ k, (((Pi.single ks 1 - a : K → ℤ) k : ℤ) : ℝ) * Real.log ‖c k‖ =
      (if k = ks then Real.log ‖c k‖ else 0) + (dh k : ℝ) * Real.log ‖c k‖ - (dg k : ℝ) * Real.log ‖c k‖ := by
    intro k
    have a1 : (dg k : ℝ) = dh k + a k := by exact_mod_cast hd k
    rw [a1]
    by_cases hk : k = ks
    · subst hk
      simp
      ring
    · simp [hk]
      ring
  simp only [e4, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem exists_flat (y : (Σ k, ι k) → Ω) (hP : IsMultiHomogIdeal (mCoordIdeal y)) (a : K → ℤ) (ks : K)
    (hcov : ∀ z ∈ mcPts (mCoordIdeal y), ∃ d, Rep y a ks d ∧ NZ d z) :
    ∃ T : HermLine ι, IsSmoothHerm T ∧ T.a = Pi.single ks 1 - a ∧
      ∀ (D : ℕ) (J : Ideal (MRing ι)) (R : AnLogRes (mCoordIdeal y) J D), Chg.IsFlatOn R T := by
  classical
  let F : HermLine ι := GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (Pi.single ks 1 - a)
  have hF : IsSmoothHerm F := GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι _
  have hFa : F.a = Pi.single ks 1 - a := rfl
  let ψ : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ d, Rep y a ks d ∧ NZ d z then Real.log ‖rho h.choose z‖ else 0
  have hψ : ∀ z ∈ mcPts (mCoordIdeal y), ∀ d, Rep y a ks d → NZ d z → ψ z = Real.log ‖rho d z‖ := by
    intro z hz d h1 h2
    have h : ∃ d, Rep y a ks d ∧ NZ d z := ⟨d, h1, h2⟩
    simp only [ψ, dif_pos h]
    rw [rho_eq h.choose_spec.1 h1 hz h.choose_spec.2 h2]
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_of_local_smooth K ι (mCoordIdeal y)
    (fun z => ψ z - Real.log (F.h z)) hP (by
      rintro z hz z' ⟨c, hc, rfl⟩
      obtain ⟨d, h1, h2⟩ := hcov z hz
      obtain ⟨n1, n2⟩ := NZ_smul h1 h2 hc
      have hz' := mcPts_smul hP c hc hz
      beta_reduce
      rw [hψ _ hz' d h1 n1, hψ _ hz d h1 h2, n2, Chg.log_h_smul F hc hz.1, hFa]
      ring) (by
      intro z hz
      obtain ⟨d, h1, h2⟩ := hcov z hz
      have ho : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
        rw [Set.setOf_forall]
        refine isOpen_iInter_of_finite fun k => ?_
        rw [Set.setOf_exists]
        exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨{z | NZ d z} ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, fun z => Real.log ‖rho d z‖ - Real.log (F.h z),
        (isOpen_NZ d).inter ho, ⟨h2, hz.1⟩, ?_, ?_⟩
      · refine ContDiffOn.sub ?_ ((hF.mono Set.inter_subset_right).log fun w hw => (F.pos w hw.2).ne')
        intro w hw
        have a1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rho d) w :=
          ((analytic_rho hw.1).contDiffAt (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
        exact ((a1.norm ℝ (rho_ne hw.1)).log (norm_ne_zero_iff.2 (rho_ne hw.1))).contDiffWithinAt
      · intro w hw
        beta_reduce
        rw [hψ w hw.2 d h1 hw.1.1])
  refine ⟨B.tensor F, ContDiffOn.mul hBs hF, by show B.a + F.a = _; rw [hBa, zero_add, hFa], ?_⟩
  intro D J R x _
  have hx := R.mem x x (R.mem_U x)
  obtain ⟨d, h1, h2⟩ := hcov _ hx
  have hl : ∀ j z, z ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x →
      AnalyticAt ℂ (fun z => R.lift x ((R.A.chart j).symm z)) z := fun j z hz =>
    AnalyticAt.pi fun p => R.holo x p j z hz
  have hf : ∀ f : MRing ι, R.A.HoloOn (R.U x) fun w => aeval (R.lift x w) f := fun f j z hz =>
    (analytic_aeval f _).comp (hl j z hz)
  obtain ⟨V0, o0, m0, s0, L0, l0, e0⟩ := Chg.Twist.exists_log R.A (R.isOpen_U x) (R.holo x ⟨ks, d.1⟩) (R.mem_U x) h2.1
  obtain ⟨V1, o1, m1, -, L1, l1, e1⟩ := Chg.Twist.exists_log R.A (R.isOpen_U x) (hf d.2.1) (R.mem_U x) h2.2.1
  obtain ⟨V2, o2, m2, -, L2, l2, e2⟩ := Chg.Twist.exists_log R.A (R.isOpen_U x) (hf d.2.2) (R.mem_U x) h2.2.2
  refine ⟨V0 ∩ V1 ∩ V2, (o0.inter o1).inter o2, ⟨⟨m0, m1⟩, m2⟩, fun w => L0 w + L2 w - L1 w, ?_, ?_⟩
  · rintro j z ⟨hz, ⟨z0, z1⟩, z2⟩
    exact ((l0 j z ⟨hz, z0⟩).add (l2 j z ⟨hz, z2⟩)).sub (l1 j z ⟨hz, z1⟩)
  · rintro w ⟨⟨w0, w1⟩, w2⟩
    have hw := R.mem x w (s0 w0)
    obtain ⟨n0, f0⟩ := e0 w w0
    obtain ⟨n1, f1⟩ := e1 w w1
    obtain ⟨n2, f2⟩ := e2 w w2
    have hn : NZ d (R.lift x w) := ⟨n0, n1, n2⟩
    show Real.log (B.h (R.lift x w) * F.h (R.lift x w)) - 0 = _
    rw [Real.log_mul (B.pos _ hw.1).ne' (F.pos _ hw.1).ne', hB _ hw, hψ _ hw d h1 hn]
    simp only [Complex.sub_re, Complex.add_re, f0, f1, f2, rho]
    rw [norm_div, norm_mul, Real.log_div (mul_ne_zero (norm_ne_zero_iff.2 n0) (norm_ne_zero_iff.2 n2))
      (norm_ne_zero_iff.2 n1), Real.log_mul (norm_ne_zero_iff.2 n0) (norm_ne_zero_iff.2 n2)]
    ring

theorem val_ne_of_integral {A : Type} [CommRing A] [Algebra A Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (hφ : ∀ a : W, φ a ≠ 0 → IsUnit a) (hA : ∀ a : A, algebraMap A Ω a ∈ W) {r t : Ω} (hr : r ∈ W)
    (ht : IsIntegral A t) (hrt : r * t ∈ W) (h : φ ⟨_, hrt⟩ ≠ 0) : φ ⟨r, hr⟩ ≠ 0 := by
  intro h0
  let ρ : A →+* W := (algebraMap A Ω).codRestrict W hA
  obtain ⟨p, hp, e⟩ := ht
  have e1 : (p.map ρ).eval₂ W.subtype t = 0 := by
    rw [Polynomial.eval₂_map]
    exact e
  have e2 := Polynomial.scaleRoots_eval₂_eq_zero W.subtype (s := (⟨r, hr⟩ : W)) e1
  have e3 : ((p.map ρ).scaleRoots ⟨r, hr⟩).eval (⟨_, hrt⟩ : W) = 0 := by
    apply Subtype.ext
    have := Polynomial.eval₂_at_apply (p := (p.map ρ).scaleRoots ⟨r, hr⟩) W.subtype (⟨_, hrt⟩ : W)
    exact this.symm.trans e2
  have e4 := congrArg φ e3
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, Polynomial.map_scaleRoots _ _ _
    (by simp [(hp.map ρ).leadingCoeff]), h0, Polynomial.scaleRoots_zero] at e4
  simp [((hp.map ρ).map φ).leadingCoeff, h] at e4

end Flat

theorem exists_line {K₀ K : Type} [Fintype K₀] [Fintype K] [DecidableEq K] {ι₀ : K₀ → Type}
    {ι : K → Type} [∀ k, Fintype (ι₀ k)] [∀ k, Fintype (ι k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (y₀ : (Σ k, ι₀ k) → Ω₀) (y : (Σ k, ι k) → Ω) (i : Ω₀ →+* Ω) {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, ι k}
    (hv : IsBlockMap κ v) (hy : ∀ p, y (v p) = i (y₀ p)) {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (A : HermLine ι₀) (hAs : IsSmoothHerm A) {m l : ℕ} (s : Fin l → Ω₀)
    (hs : ∀ j, s j ∈ chartLatNm y₀ (fun k => m * A.a k - 1) 1)
    (hs' : ∀ z ∈ Small.ptsOver ℂ (mCoordIdeal y₀),
      ∃ (j : Fin l) (val : ℂ), val ≠ 0 ∧ Small.HasVal y₀ (fun k => m * A.a k - 1) (s j) z val)
    (ks : K) (hks : ks ∉ Set.range κ) (e : Fin l ≃ ι ks) (he : ∀ j, y ⟨ks, e j⟩ = i (s j)) (n : ℕ) :
    ∃ H : HermLine ι, IsSmoothHerm H ∧ H.a = (n : ℤ) • (pullDeg κ 1 + Pi.single ks 1) ∧
      ∀ (J : Ideal (MRing ι)) (R : AnLogRes (mCoordIdeal y) J D),
        PB.SamePot R.A Set.univ (potOf R H) ((potOf R (pullHerm hv A)).rsmul ((n : ℝ) * m)) := by
  classical
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hA.2.1.2.1
  have hren : ∀ f : MRing ι₀, aeval y (rename v f) = i (aeval y₀ f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, rename_X, aeval_X, hy]
  have hle : mCoordIdeal y₀ ≤ imageZ v (mCoordIdeal y) := by
    intro f hf
    let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp i) fun k => MvPolynomial.X (κ k)
    have key : ∀ f : MRing ι₀, mConeMap y (rename v f) = Φ (mConeMap y₀ f) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a => simp [mConeMap, Φ]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp, rename_X]
        congr 1
        simp [mConeMap, Φ, hy, hv.2.2.1]
    have hf' : mConeMap y₀ f = 0 := hf
    show mConeMap y (rename v f) = 0
    rw [key, hf', map_zero]
  set a₀ : K₀ → ℤ := fun k => m * A.a k - 1 with ha₀
  have hprod : ∀ {G : Type} [Field G] (x : K → G) (b : K₀ → ℤ), ∏ k, x k ^ pullDeg κ b k = ∏ k, x (κ k) ^ b k := by
    intro G _ x b
    symm
    refine Finset.prod_of_injOn κ hv.1.injOn (by simp) (fun k _ hk => ?_) fun k _ => ?_
    · rw [pullDeg, Function.extend_apply' _ _ _ (by simpa using hk)]
      simp
    · rw [pullDeg, hv.1.extend_apply]
  have hcov : ∀ z ∈ mcPts (mCoordIdeal y), ∃ d, Flat.Rep y (pullDeg κ a₀) ks d ∧ Flat.NZ d z := by
    intro z hz
    have hz₀ := Chg.mem_mcPts_restr hv hle hz
    obtain ⟨j, val, hval, dg, dh, g, h, hg, hh, hd, e1, e2, e3⟩ := hs' _ (Flat.mem_ptsOver hz₀)
    have hG := Chg.DegBlock.isMultiHomog_rename' hv hg
    have hH := Chg.DegBlock.isMultiHomog_rename' hv hh
    have hD : ∀ k, ((Function.extend κ dg 0 k : ℕ) : ℤ) = (Function.extend κ dh 0 k : ℕ) + pullDeg κ a₀ k := by
      intro k
      by_cases hk : ∃ b, κ b = k
      · obtain ⟨b, rfl⟩ := hk
        simp only [pullDeg, hv.1.extend_apply]
        exact hd b
      · simp [pullDeg, Function.extend_apply' _ _ _ hk]
    have hE : aeval y (rename v g) = y ⟨ks, e j⟩ * aeval y (rename v h) := by
      rw [hren, hren, e1, map_mul, he]
    have z2 : aeval z (rename v h) ≠ 0 := by rw [aeval_rename]; exact e2
    have z3 : aeval z (rename v g) = val * aeval z (rename v h) := by
      rw [aeval_rename, aeval_rename]; exact e3
    refine ⟨⟨e j, rename v g, rename v h⟩, ⟨_, _, hG, hH, hD, hE⟩, ?_, by rw [z3]; exact mul_ne_zero hval z2, z2⟩
    obtain ⟨W, φ, hφ, hW1, hW2⟩ := LocVal.exists_locRing_val K ι Ω y z (Flat.mem_ptsOver hz)
    choose C hC using hz.1
    have hyC : ∀ q, z q ≠ 0 → y q ≠ 0 := fun q hq h0 => by
      apply hq
      have hm : (X q : MRing ι) ∈ mCoordIdeal y := by
        show mConeMap y (X q) = 0
        simp [mConeMap, h0]
      simpa using hz.2 _ hm
    have hC₀ : ∀ k : K₀, ∃ b : ι₀ k, v ⟨k, b⟩ = ⟨κ k, C (κ k)⟩ := fun k => by
      obtain ⟨⟨pk, pi⟩, hp⟩ := hv.2.2.2 ⟨κ k, C (κ k)⟩ ⟨k, rfl⟩
      have h2 : pk = k := hv.1 (by rw [← hv.2.2.1 ⟨pk, pi⟩, hp])
      subst h2
      exact ⟨pi, hp⟩
    choose C₀ hC₀ using hC₀
    have hy₀ : ∀ k, y₀ ⟨k, C₀ k⟩ ≠ 0 := fun k h0 => hyC _ (hC (κ k)) (by rw [← hC₀, hy, h0, map_zero])
    obtain ⟨w1, w2⟩ := hW2 (pullDeg κ a₀) (y ⟨ks, e j⟩) val C ⟨_, _, _, _, hG, hH, hD, hE, z2, z3⟩ hC
    obtain ⟨r1, r2⟩ := hW1 ks (C ks) (e j) (hC ks)
    have hint : IsIntegral (chartRingZ y₀ C₀) _ := hs (e.symm (C ks)) C₀ hy₀
    letI : Algebra (chartRingZ y₀ C₀) Ω := (i.comp (chartRingZ y₀ C₀).val.toRingHom).toAlgebra
    let i' : Ω₀ →ₐ[chartRingZ y₀ C₀] Ω := { i with commutes' := fun _ => rfl }
    have hint' := hint.map i'
    have hAW : ∀ x : chartRingZ y₀ C₀, algebraMap (chartRingZ y₀ C₀) Ω x ∈ W := by
      rintro ⟨x, hx⟩
      show i x ∈ W
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨⟨k, b⟩, rfl⟩ := hx
        rw [map_div₀, ← hy, ← hy, hC₀]
        have hq := hv.2.2.1 ⟨k, b⟩
        generalize v ⟨k, b⟩ = q at hq
        obtain ⟨k', b'⟩ := q
        simp only at hq
        subst hq
        exact (hW1 _ _ b' (hC _)).1
      | algebraMap r => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | mul _ _ _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
    have heq : y ⟨ks, e j⟩ / y ⟨ks, C ks⟩ *
        i' (s (e.symm (C ks)) * ∏ k, y₀ ⟨k, C₀ k⟩ ^ (-(((1 : ℕ) : ℤ) * a₀ k))) =
        y ⟨ks, e j⟩ * ∏ k, y ⟨k, C k⟩ ^ (-pullDeg κ a₀ k) := by
      have q1 : i (s (e.symm (C ks))) = y ⟨ks, C ks⟩ := by rw [← he, Equiv.apply_symm_apply]
      have q2 : ∏ k, y ⟨k, C k⟩ ^ (-pullDeg κ a₀ k) = ∏ k, i (y₀ ⟨k, C₀ k⟩) ^ (-a₀ k) := by
        simp only [zpow_neg, Finset.prod_inv_distrib]
        rw [hprod (fun k => y ⟨k, C k⟩) a₀]
        simp only [← hy, hC₀]
      show _ * i _ = _
      rw [map_mul, map_prod, q1, q2, ← mul_assoc, div_mul_cancel₀ _ (hyC _ (hC ks))]
      simp only [map_zpow₀, Nat.cast_one, one_mul]
    have key := Flat.val_ne_of_integral W φ hφ hAW r1 hint' (heq ▸ w1) (by
      intro h0
      apply hval
      rw [← w2]
      have : φ ⟨_, w1⟩ = 0 := by
        rw [← h0]
        congr 2
        exact heq.symm
      rw [this, zero_mul])
    show z ⟨ks, e j⟩ ≠ 0
    rw [← r2]
    exact mul_ne_zero key (hC ks)
  obtain ⟨T, hT, hTa, hTf⟩ := Flat.exists_flat y hP (pullDeg κ a₀) ks hcov
  have hpA := Chg.isSmoothHerm_pull hv hAs
  refine ⟨PB.combLine ![pullHerm hv A, T] ![((n * m : ℕ) : ℤ), (n : ℤ)], ?_, ?_, ?_⟩
  · have : (PB.combLine ![pullHerm hv A, T] ![((n * m : ℕ) : ℤ), (n : ℤ)]).h =
        fun z => (pullHerm hv A).h z ^ (n * m) * T.h z ^ n := by
      funext z
      simp only [PB.combLine_h, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast]
    unfold IsSmoothHerm
    rw [this]
    exact (ContDiffOn.pow hpA _).mul (ContDiffOn.pow hT _)
  · funext k
    simp only [PB.combLine_a, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hTa]
    show _ * pullDeg κ A.a k + _ = _
    by_cases hk : ∃ b, κ b = k
    · obtain ⟨b, rfl⟩ := hk
      simp only [pullDeg, hv.1.extend_apply, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, ha₀, Pi.one_apply, smul_eq_mul]
      push_cast
      ring
    · simp [pullDeg, Function.extend_apply' _ _ _ hk]
  · intro J R x _
    obtain ⟨V, oV, mV, G, hG, eG⟩ := hTf D J R x trivial
    refine ⟨V ∩ R.U x, oV.inter (R.isOpen_U x), ⟨mV, R.mem_U x⟩, fun w => ((n : ℝ) : ℂ) * G w, ?_, ?_⟩
    · rintro j z ⟨hz, hz', -⟩
      exact analyticAt_const.mul (hG j z ⟨hz, hz'⟩)
    · rintro w ⟨w1, w2⟩
      have hw := (R.mem x w w2).1
      have E : Real.log (T.h (R.lift x w)) - 0 = (G w).re := eG w w1
      show Real.log ((PB.combLine ![pullHerm hv A, T] ![((n * m : ℕ) : ℤ), (n : ℤ)]).h (R.lift x w)) -
        (n : ℝ) * m * Real.log ((pullHerm hv A).h (R.lift x w)) = _
      simp only [PB.combLine_h, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast]
      rw [Real.log_mul (pow_ne_zero _ ((pullHerm hv A).pos _ hw).ne') (pow_ne_zero _ (T.pos _ hw).ne'),
        Real.log_pow, Real.log_pow, Complex.re_ofReal_mul, ← E]
      push_cast
      ring

end RootFieldNumerics.Ref
