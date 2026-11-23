import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TBNFinal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelThreeSeparatesTangents
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology

namespace GlobalTheory

namespace ThetaJet

section Algebra

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem spans_mod_pow_succ (m : Ideal R) (J A B : Submodule k R) (D : ℕ)
    (hJ : ∀ x, ∃ s ∈ J, x - s ∈ m ^ 2) (hA : ∀ x, ∃ a ∈ A, x - a ∈ m ^ (D + 1))
    (hB : ∀ a ∈ A, ∀ s ∈ J, a * s ∈ B) (x : R) : ∃ b ∈ B, x - b ∈ m ^ (D + 2) := by
  set I : Ideal R := Ideal.span {s | s ∈ J ∧ s ∈ m} with hI
  have h2 : m ^ 2 ≤ m := Ideal.pow_le_self two_ne_zero
  have hm1 : m ≤ I ⊔ m ^ 2 := by
    intro y hy
    obtain ⟨s, hs, hs'⟩ := hJ y
    have : s ∈ m := by simpa using m.sub_mem hy (h2 hs')
    have e : y = s + (y - s) := by ring
    rw [e]
    exact Submodule.add_mem_sup (Ideal.subset_span ⟨hs, this⟩) hs'
  have hm : ∀ n, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc m ^ (n + 1) = m * m ^ n := pow_succ' _ _
        _ ≤ (I ⊔ m ^ 2) * m ^ n := Ideal.mul_mono_left hm1
        _ = I * m ^ n ⊔ m ^ (n + 1 + 1) := by
          rw [Ideal.sup_mul, ← pow_add]; congr 2; omega
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_left _
  have hIB : ∀ z ∈ I, ∀ y, ∃ b ∈ B, y * z - b ∈ m ^ (D + 2) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem s hs =>
      intro y
      obtain ⟨a, ha, ha'⟩ := hA y
      refine ⟨a * s, hB a ha s hs.1, ?_⟩
      rw [← sub_mul, pow_succ]
      exact Ideal.mul_mem_mul ha' hs.2
    | zero => intro y; exact ⟨0, B.zero_mem, by simp⟩
    | add z w _ _ hz hw =>
      intro y
      obtain ⟨b, hb, hb'⟩ := hz y
      obtain ⟨c, hc, hc'⟩ := hw y
      refine ⟨b + c, B.add_mem hb hc, ?_⟩
      have e : y * (z + w) - (b + c) = (y * z - b) + (y * w - c) := by ring
      rw [e]
      exact Ideal.add_mem _ hb' hc'
    | smul c z _ hz =>
      intro y
      rw [smul_eq_mul, ← mul_assoc]
      exact hz _
  obtain ⟨s, hs, hs'⟩ := hJ 1
  obtain ⟨a, ha, ha'⟩ := hA x
  have h1 : x - a * s ∈ m := by
    have e : x - a * s = (x - a) + a * (1 - s) := by ring
    rw [e]
    exact m.add_mem (Ideal.pow_le_self (Nat.succ_ne_zero _) ha') (m.mul_mem_left _ (h2 hs'))
  obtain ⟨z, hz, w, hw, e⟩ := Submodule.mem_sup.1 (hm (D + 1) h1)
  obtain ⟨b, hb, hb'⟩ := hIB z hz 1
  refine ⟨a * s + b, B.add_mem (hB a ha s hs) hb, ?_⟩
  have e' : x - (a * s + b) = (1 * z - b) + w := by linear_combination -e
  rw [e']
  exact Ideal.add_mem _ hb' hw

end Algebra

variable {ι : Type} [Fintype ι]

noncomputable def powTorus (Y : GT ι) (k : ℕ) : GT ι :=
  { Y with
    ka := fun γ => Y.ka γ ^ k
    ka_abs := fun x hx => by rw [norm_pow, Y.ka_abs x hx, one_pow] }

def TwistedLaw (Y : GT ι) (k : ℕ) (c : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, ∀ v, F (v + γ) = Y.ka γ ^ k *
    cexp (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2) * F v

theorem Hf_add_left (v w γ : EuclideanSpace ℂ ι) : Hf (v + w) γ = Hf v γ + Hf w γ := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

theorem twistedLaw_zero_iff (Y : GT ι) (k : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    TwistedLaw Y k 0 F ↔ F ∈ (powTorus Y k).Sec k := by
  have : ∀ γ : EuclideanSpace ℂ ι, Hf 0 γ = 0 := fun γ => by simp [Hf]
  simp only [TwistedLaw, this, mul_zero, add_zero]
  rfl

theorem TwistedLaw.mul {Y : GT ι} {k l : ℕ} {c d : EuclideanSpace ℂ ι}
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : TwistedLaw Y k c F) (hG : TwistedLaw Y l d G) :
    TwistedLaw Y (k + l) (c + d) (F * G) := by
  refine ⟨hF.1.mul hG.1, fun γ hγ v => ?_⟩
  simp only [Pi.mul_apply]
  rw [hF.2 γ hγ, hG.2 γ hγ, Hf_add_left]
  have e : ((k + l : ℕ) : ℂ) * Real.pi * Hf v γ + Real.pi * (Hf c γ + Hf d γ)
      + ((k + l : ℕ) : ℂ) * Real.pi * Hf γ γ / 2 =
      (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2) +
      (l * Real.pi * Hf v γ + Real.pi * Hf d γ + l * Real.pi * Hf γ γ / 2) := by
    push_cast; ring
  rw [e, Complex.exp_add (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2)]
  ring

theorem twistedLaw_translate {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1)
    (a : EuclideanSpace ℂ ι) : TwistedLaw Y 1 a (fun v => θ (v + a)) := by
  refine ⟨hθ.1.comp (differentiable_id.add_const a), fun γ hγ v => ?_⟩
  have := hθ.2 γ hγ (v + a)
  rw [Hf_add_left] at this
  simp only
  rw [add_right_comm, this]
  congr 2
  · simp
  · congr 1; push_cast; ring

theorem TwistedLaw.pow {Y : GT ι} {c : EuclideanSpace ℂ ι}
    {F : EuclideanSpace ℂ ι → ℂ} (hF : TwistedLaw Y 1 c F) (p : ℕ) :
    TwistedLaw Y p (p • c) (F ^ p) := by
  induction p with
  | zero => exact ⟨by simp, fun γ _ v => by simp [Hf]⟩
  | succ p ih => rw [pow_succ, succ_nsmul]; exact ih.mul hF

theorem analyticAt_of_differentiable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : AnalyticAt ℂ F x :=
  SCV.analyticAt_of_differentiableOn (s := Set.univ) hF.differentiableOn univ_mem

theorem exists_sec_ne_zero {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1)
    (h0 : θ ≠ 0) {r : ℕ} (hr : 2 ≤ r) : ∃ F ∈ (powTorus Y r).Sec r, F 0 ≠ 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  have hp : -(p : ℂ) ≠ 0 := by
    rw [neg_ne_zero, Nat.cast_ne_zero]; omega
  have hd : Differentiable ℂ θ := hθ.1
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ => analyticAt_of_differentiable hd x
  set U : Set (EuclideanSpace ℂ ι) := {x | θ x ≠ 0} with hU
  have ho : IsOpen U := isOpen_ne_fun hd.continuous continuous_const
  have hden : Dense U := by
    intro x
    by_contra hx
    apply h0
    refine han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hy'
    exact hy (subset_closure hy')
  obtain ⟨a, ha, hb, -⟩ := exists_mem_four_of_open_dense ho hden (Homeomorph.refl _)
    (Homeomorph.smulOfNeZero _ hp) (Homeomorph.refl _) (Homeomorph.refl _)
  have ha' : θ a ≠ 0 := ha
  have hb' : θ (-(p • a)) ≠ 0 := by
    have : θ ((-(p : ℂ)) • a) ≠ 0 := hb
    rwa [neg_smul, Nat.cast_smul_eq_nsmul] at this
  have h := ((twistedLaw_translate hθ a).pow p).mul (twistedLaw_translate hθ (-(p • a)))
  rw [add_neg_cancel, twistedLaw_zero_iff] at h
  exact ⟨_, h, by simp [ha', hb']⟩

open Classical in

noncomputable def jets (Y : GT ι) (k : ℕ) : Submodule ℂ (MvPowerSeries ι ℂ) where
  carrier := {x | ∃ F ∈ (powTorus Y k).Sec k,
    taylorDir (fun i => EuclideanSpace.single i (1 : ℂ)) F = x}
  add_mem' := by
    rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
    exact ⟨F + G, add_mem hF hG, taylorDir_add _ (analyticAt_of_differentiable hF.1 0)
      (analyticAt_of_differentiable hG.1 0)⟩
  zero_mem' := ⟨0, zero_mem _, taylorDir_zero _⟩
  smul_mem' := by
    rintro c _ ⟨F, hF, rfl⟩
    exact ⟨c • F, Submodule.smul_mem _ c hF,
      taylorDir_smul _ c (analyticAt_of_differentiable hF.1 0)⟩

theorem mul_mem_jets {Y : GT ι} {k l : ℕ} {x y : MvPowerSeries ι ℂ} (hx : x ∈ jets Y k)
    (hy : y ∈ jets Y l) : x * y ∈ jets Y (k + l) := by
  obtain ⟨F, hF, rfl⟩ := hx
  obtain ⟨G, hG, rfl⟩ := hy
  have h := ((twistedLaw_zero_iff Y k F).2 hF).mul ((twistedLaw_zero_iff Y l G).2 hG)
  rw [add_zero, twistedLaw_zero_iff] at h
  exact ⟨_, h, taylorDir_mul _ (analyticAt_of_differentiable hF.1 0)
      (analyticAt_of_differentiable hG.1 0)⟩

theorem coeff_single_taylorDir {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorDir u F) = fderiv ℂ F 0 (u i) := by
  have h := congrArg MvPowerSeries.constantCoeff (taylorDir_fderiv u hF i)
  rw [constantCoeff_taylorDir, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_pderiv] at h
  simpa using h.symm

theorem sub_affine_mem_sq {σ : Type*} [Fintype σ] (x : MvPowerSeries σ ℂ) :
    x - (MvPowerSeries.constantCoeff x • (1 : MvPowerSeries σ ℂ) +
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) x • (MvPowerSeries.X i : MvPowerSeries σ ℂ))
      ∈ germIdeal σ ℂ ^ 2 := by
  classical
  refine mem_germIdeal_pow_iff.2 fun d hd => ?_
  by_cases h : d = 0
  · subst h
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, d = Finsupp.single j 1 := by
      have h1 : d.degree = 1 := by
        have : d.degree ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
        omega
      have : d ∈ Set.range fun a => Finsupp.single a 1 := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    simp [MvPowerSeries.coeff_one, MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem jets_three {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (x : MvPowerSeries ι ℂ) : ∃ s ∈ jets Y 3, x - s ∈ germIdeal ι ℂ ^ 2 := by
  classical
  have key : jets Y 3 ⊔ (germIdeal ι ℂ ^ 2).restrictScalars ℂ = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hform : ∀ y, φ y = MvPowerSeries.constantCoeff y * φ 1 +
        ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) y * φ (MvPowerSeries.X i) := by
      intro y
      have := hφ (Submodule.mem_sup_right (T := (germIdeal ι ℂ ^ 2).restrictScalars ℂ)
        (sub_affine_mem_sq y))
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [this]
      simp
    set c : EuclideanSpace ℂ ι := ∑ i, φ (MvPowerSeries.X i) • EuclideanSpace.single i (1 : ℂ)
      with hc
    obtain ⟨h1, h2⟩ := level_three_separates_tangents Y θ hθ h0 (φ 1) c fun a b => by
      have h := ((twistedLaw_translate hθ a).mul (twistedLaw_translate hθ b)).mul
        (twistedLaw_translate hθ (-a - b))
      rw [show a + b + (-a - b) = 0 by abel, twistedLaw_zero_iff] at h
      have e : (((fun v => θ (v + a)) * fun v => θ (v + b)) * fun v => θ (v + (-a - b))) =
          fun v => θ (v + a) * θ (v + b) * θ (v - a - b) := by
        funext v
        simp only [Pi.mul_apply]
        congr 2
        abel
      rw [e] at h
      have h3 := hφ (Submodule.mem_sup_left (S := jets Y 3) ⟨_, h, rfl⟩)
      rw [LinearMap.mem_ker, hform, constantCoeff_taylorDir] at h3
      simp only [coeff_single_taylorDir _ (analyticAt_of_differentiable h.1 0)] at h3
      rw [hc, map_sum, ← h3]
      simp only [map_smul, smul_eq_mul, zero_add, zero_sub]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 : ∀ i, φ (MvPowerSeries.X i) = 0 := fun i => by
      have := congrArg (fun v : EuclideanSpace ℂ ι => v i) (hc.symm.trans h1)
      simpa [Pi.single_apply] using this
    apply hφ0
    ext y
    rw [hform]
    simp [h2, h3]
  obtain ⟨s, hs, w, hw, e⟩ := Submodule.mem_sup.1 (key ▸ Submodule.mem_top (x := x))
  exact ⟨s, hs, by rw [← e, add_sub_cancel_left]; exact hw⟩

theorem jets_span {Y : GT ι} {θ : EuclideanSpace ℂ ι → ℂ} (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    {r : ℕ} (hr : 2 ≤ r) (D : ℕ) (x : MvPowerSeries ι ℂ) :
    ∃ s ∈ jets Y (r + 3 * D), x - s ∈ germIdeal ι ℂ ^ (D + 1) := by
  induction D generalizing x with
  | zero =>
    obtain ⟨F, hF, hF0⟩ := exists_sec_ne_zero hθ h0 hr
    refine ⟨(MvPowerSeries.constantCoeff x / F 0) • _, Submodule.smul_mem _ _ ⟨F, hF, rfl⟩, ?_⟩
    refine mem_germIdeal_pow_iff.2 fun d hd => ?_
    obtain rfl : d = 0 := by simpa [Finsupp.degree_eq_zero_iff] using hd
    simp [MvPowerSeries.smul_eq_C_mul, hF0]
  | succ D ih =>
    exact spans_mod_pow_succ _ (jets Y 3) _ _ D (jets_three hθ h0) ih
      (fun a ha s hs => mul_mem_jets ha hs) x

end ThetaJet

open ThetaJet

open Classical in

theorem exists_section_jet_ne_zero {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (D q : ℕ) (hq : 3 * D + 2 ≤ q) (P : MvPolynomial ι ℂ) (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    ∃ F : EuclideanSpace ℂ ι → ℂ, Differentiable ℂ F ∧
      (∀ γ ∈ lat Y.b, ∀ v, F (v + γ) = Y.ka γ ^ q * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v) ∧
      polyDeriv P (fun i => EuclideanSpace.single i 1) F 0 ≠ 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 * D := ⟨q - 3 * D, by omega⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hP
  obtain ⟨_, ⟨F, hF, rfl⟩, hs⟩ :=
    jets_span hθ h0 (r := r) (by omega) D (MvPowerSeries.monomial m 1)
  refine ⟨F, hF.1, hF.2, ?_⟩
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, Finset.sum_congr rfl (g := fun d => P.coeff d *
    ((∏ i, (d i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff d (MvPowerSeries.monomial m (1 : ℂ))),
    Finset.sum_eq_single m]
  · rw [MvPowerSeries.coeff_monomial_same, mul_one]
    exact mul_ne_zero hm (cast_prod_factorial_ne_zero m)
  · intro d _ hd
    rw [MvPowerSeries.coeff_monomial_ne hd, mul_zero]
  · intro h
    exact absurd (MvPolynomial.mem_support_iff.2 hm) h
  · intro d hd
    have h1 : d.degree ≤ D := (MvPolynomial.le_totalDegree hd).trans hD
    have h2 := mem_germIdeal_pow_iff.1 hs d (by omega)
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]

end GlobalTheory
