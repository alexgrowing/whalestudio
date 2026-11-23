import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingHolomorphicExpLogConvexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierExponentialHolomorphicLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleHolomorphicCoboundaryLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicCocycleTranslationCoboundaryStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FactorDegreeZero

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem per_add' (t : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per t (x + y) = per t x + per t y := by
  ext i
  simp only [per, Pi.add_apply, Complex.ofReal_add, Matrix.vecMul, dotProduct, add_mul,
    Finset.sum_add_distrib]
  ring

theorem per_single_inr (t : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    per t (Pi.single (Sum.inr k) 1) = Pi.single k 1 := by
  ext i
  by_cases h : i = k
  · subst h; simp [per, Matrix.vecMul, dotProduct, Pi.single_apply]
  · simp [per, Matrix.vecMul, dotProduct, Pi.single_apply, h]

theorem transl_inr (τ : E → Matrix (Fin g) (Fin g) ℂ) (k : Fin g) (P : Pt E g) :
    transl τ (Pi.single (Sum.inr k) 1) P = (P.1, P.2 + Pi.single k 1) := by
  simp [transl, per_single_inr]

theorem transl_transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ x (transl τ y P) = transl τ (x + y) P := by
  simp only [transl, per_add']
  ext <;> simp [add_assoc, add_comm]

theorem transl_comm (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ x (transl τ y P) = transl τ y (transl τ x P) := by
  rw [transl_transl, transl_transl, add_comm]

theorem transl_shift (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) (v : Fin g → ℂ) :
    transl τ x (P.1, P.2 + v) = ((transl τ x P).1, (transl τ x P).2 + v) := by
  simp only [transl]
  ext <;> simp [add_right_comm]

theorem transl_mem {U : Set E} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) {P : Pt E g}
    (hP : P ∈ cov U g) : transl τ x P ∈ cov U g :=
  ⟨hP.1, Set.mem_univ _⟩

theorem single_mem_stdLat (i : Fin g ⊕ Fin g) : (Pi.single i 1 : Fl g) ∈ stdLat g :=
  Submodule.subset_span ⟨i, by simp [Pi.basisFun_apply]⟩

theorem differentiableOn_transl {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : ∀ i j, DifferentiableOn ℂ (fun b => τ b i j) U) (x : Fl g) :
    DifferentiableOn ℂ (transl τ x) (cov U g) := by
  have hper : DifferentiableOn ℂ (fun b => per (τ b) x) U := by
    refine differentiableOn_pi.2 fun i => ?_
    simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
    exact (DifferentiableOn.fun_sum fun j _ => (hτ j i).const_mul _).add_const _
  exact differentiableOn_fst.prodMk (differentiableOn_snd.add
    (hper.comp differentiableOn_fst fun P hP => hP.1))

theorem eq_of_eq_on_basis {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (j j' : Fl g → Pt E g → ℂ)
    (hj : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, j (l + l') P = j l (transl τ l' P) * j l' P)
    (hj0 : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, j l P ≠ 0)
    (hj' : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, j' (l + l') P = j' l (transl τ l' P) * j' l' P)
    (hj0' : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, j' l P ≠ 0)
    (hgen : ∀ i, ∀ P ∈ cov U g, j (Pi.single i 1) P = j' (Pi.single i 1) P) :
    ∀ l ∈ stdLat g, ∀ P ∈ cov U g, j l P = j' l P := by
  have hzero : ∀ (k : Fl g → Pt E g → ℂ),
      (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, k (l + l') P = k l (transl τ l' P) * k l' P) →
      (∀ l ∈ stdLat g, ∀ P ∈ cov U g, k l P ≠ 0) → ∀ P ∈ cov U g, k 0 P = 1 := by
    intro k hk hk0 P hP
    have h := hk 0 (zero_mem _) 0 (zero_mem _) P hP
    have ht : transl τ 0 P = P := by
      have : per (τ P.1) 0 = 0 := by simpa using per_add' (τ P.1) 0 0
      simp [transl, this]
    rw [add_zero, ht] at h
    have h0 := hk0 0 (zero_mem _) P hP
    exact (mul_left_eq_self₀.1 h.symm).resolve_right h0
  have hneg : ∀ (k : Fl g → Pt E g → ℂ),
      (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, k (l + l') P = k l (transl τ l' P) * k l' P) →
      (∀ l ∈ stdLat g, ∀ P ∈ cov U g, k l P ≠ 0) →
      ∀ l ∈ stdLat g, ∀ P ∈ cov U g, k (-l) P = (k l (transl τ (-l) P))⁻¹ := by
    intro k hk hk0 l hl P hP
    have h := hk l hl (-l) (neg_mem hl) P hP
    rw [add_neg_cancel, hzero k hk hk0 P hP] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have key : ∀ l ∈ (stdLat g).toAddSubgroup, l ∈ stdLat g ∧ ∀ P ∈ cov U g, j l P = j' l P := by
    intro l hl
    rw [stdLat, Submodule.span_int_eq_addSubgroupClosure] at hl
    induction hl using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨Submodule.subset_span ⟨i, rfl⟩, fun P hP => ?_⟩
      simpa [Pi.basisFun_apply] using hgen i P hP
    | zero => exact ⟨zero_mem _, fun P hP => by rw [hzero j hj hj0 P hP, hzero j' hj' hj0' P hP]⟩
    | add x y _ _ hx hy =>
      refine ⟨add_mem hx.1 hy.1, fun P hP => ?_⟩
      rw [hj x hx.1 y hy.1 P hP, hj' x hx.1 y hy.1 P hP, hx.2 _ (transl_mem τ y hP), hy.2 P hP]
    | neg x _ hx =>
      refine ⟨neg_mem hx.1, fun P hP => ?_⟩
      rw [hneg j hj hj0 x hx.1 P hP, hneg j' hj' hj0' x hx.1 P hP, hx.2 _ (transl_mem τ _ hP)]
  exact fun l hl P hP => (key l hl).2 P hP

theorem factor_degree_zero_normal_form : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (u : Fl g → Pt E g → ℂ), IsFactor B τ (stdLat g) u → (∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ, (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧ ∀ z, u l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z, f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = 0) → ∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ IsPreconnected U ∧ ∃ s : Fl g → E → ℂ, (∀ l ∈ stdLat g, ContinuousOn (s l) U) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b ∈ U, s (l + l') b = s l b + s l' b) ∧ ∃ φ : Pt E g → ℂ, IsBundleIso U τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * s l P.1)) u φ := by
  intro g E _ _ _ B τ hτ u hu hdeg b₀ hb₀
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hτ.1 b₀ hb₀
  have hcov0 : cov (Metric.ball b₀ r₀) g ⊆ cov B g := Set.prod_mono hball le_rfl
  have hV : IsOpen (cov (Metric.ball b₀ r₀) g) := Metric.isOpen_ball.prod isOpen_univ
  have hVc : Convex ℝ (cov (Metric.ball b₀ r₀) g) := (convex_ball b₀ r₀).prod convex_univ
  have hlog : ∀ i : Fin g ⊕ Fin g, ∃ A : Pt E g → ℂ, DifferentiableOn ℂ A (cov (Metric.ball b₀ r₀) g) ∧
      ∀ P ∈ cov (Metric.ball b₀ r₀) g, u (Pi.single i 1) P = Complex.exp (A P) := fun i =>
    GlobalTheory.T.nonvanishing_holomorphic_exp_log_convex hV hVc _ ((hu.1 _ (single_mem_stdLat i)).1.mono hcov0)
      (fun P hP => (hu.1 _ (single_mem_stdLat i)).2 P (hcov0 hP))
  choose A hAd hAe using hlog
  have hc : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin g ⊕ Fin g → Pt E g → ℂ, a = fun i P => A i P * (2 * π * Complex.I)⁻¹ :=
    ⟨_, rfl⟩
  have hae : ∀ i, ∀ P ∈ cov (Metric.ball b₀ r₀) g,
      u (Pi.single i 1) P = Complex.exp (2 * π * Complex.I * a i P) := by
    intro i P hP
    rw [hAe i P hP, ha_def]
    congr 1
    field_simp
  have had : ∀ i, DifferentiableOn ℂ (a i) (cov (Metric.ball b₀ r₀) g) := fun i => by
    rw [ha_def]
    exact (hAd i).mul_const _
  have hcomm := GlobalTheory.T.multiplier_exponential_holomorphic_local (τ := τ) u a hae (fun i => (had i).continuousOn)
    (fun b hb => hdeg b (hball hb))

  obtain ⟨r₁, hr₁, hb1, ψ₁, hψ₁d, hψ₁⟩ := GlobalTheory.T.cocycle_holomorphic_coboundary_local (U := Metric.ball b₀ r₀) Metric.isOpen_ball
    (fun k => a (Sum.inr k)) (fun k => had _)
    (fun k j P hP => by simpa only [transl_inr] using hcomm (Sum.inr k) (Sum.inr j) P hP)
    b₀ (Metric.mem_ball_self hr₀)
  have h10 : cov (Metric.ball b₀ r₁) g ⊆ cov (Metric.ball b₀ r₀) g := Set.prod_mono hb1 le_rfl
  have hτ1 : IsPeriodMap (Metric.ball b₀ r₁) τ := ⟨Metric.isOpen_ball,
    fun i j => (hτ.2.1 i j).mono (hb1.trans hball), fun b hb => hτ.2.2 b (hball (hb1 hb))⟩

  obtain ⟨a', ha'⟩ : ∃ a' : Fin g → Pt E g → ℂ, a' = fun k P =>
      a (Sum.inl k) P - (ψ₁ (transl τ (Pi.single (Sum.inl k) 1) P) - ψ₁ P) := ⟨_, rfl⟩
  have ha'd : ∀ k, DifferentiableOn ℂ (a' k) (cov (Metric.ball b₀ r₁) g) := fun k => by
    rw [ha']
    exact ((had _).mono h10).sub ((hψ₁d.comp (differentiableOn_transl hτ1.2.1 _)
      (fun P hP => transl_mem τ _ hP)).sub hψ₁d)
  have ha'per : ∀ k j, ∀ P ∈ cov (Metric.ball b₀ r₁) g, a' k (P.1, P.2 + Pi.single j 1) = a' k P := by
    intro k j P hP
    have h1 := hcomm (Sum.inl k) (Sum.inr j) P (h10 hP)
    rw [transl_inr] at h1
    have h2 := hψ₁ j (transl τ (Pi.single (Sum.inl k) 1) P) (transl_mem τ _ hP)
    have h3 := hψ₁ j P hP
    have h4 := transl_shift τ (Pi.single (Sum.inl k) 1) P (Pi.single j 1)
    rw [ha']
    dsimp only
    rw [h4]
    linear_combination h1 - h2 + h3
  have ha'comm : ∀ k j, ∀ P ∈ cov (Metric.ball b₀ r₁) g,
      a' k (transl τ (Pi.single (Sum.inl j) 1) P) + a' j P =
      a' j (transl τ (Pi.single (Sum.inl k) 1) P) + a' k P := by
    intro k j P hP
    have h1 := hcomm (Sum.inl k) (Sum.inl j) P (h10 hP)
    have h2 := transl_comm τ (Pi.single (Sum.inl k) 1) (Pi.single (Sum.inl j) 1) P
    rw [ha']
    dsimp only
    rw [h2]
    linear_combination h1
  obtain ⟨r₂, hr₂, hb2, ψ₂, s', hψ₂d, hψ₂per, hs'c, hψ₂⟩ :=
    GlobalTheory.T.periodic_cocycle_translation_coboundary hτ1 a' ha'd ha'per ha'comm b₀ (Metric.mem_ball_self hr₁)
  have h21 : cov (Metric.ball b₀ r₂) g ⊆ cov (Metric.ball b₀ r₁) g := Set.prod_mono hb2 le_rfl
  obtain ⟨s, hs⟩ : ∃ s : Fl g → E → ℂ, s = fun l b => ∑ k, (l (Sum.inl k) : ℂ) * s' k b := ⟨_, rfl⟩
  have hsadd : ∀ l l' b, s (l + l') b = s l b + s l' b := by
    intro l l' b
    simp only [hs, Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  obtain ⟨φ, hφ⟩ : ∃ φ : Pt E g → ℂ, φ = fun P => Complex.exp (2 * π * Complex.I * (ψ₁ P + ψ₂ P)) :=
    ⟨_, rfl⟩
  have hφd : DifferentiableOn ℂ φ (cov (Metric.ball b₀ r₂) g) := by
    rw [hφ]
    exact (((hψ₁d.mono h21).add hψ₂d).const_mul _).cexp
  have hφ0 : ∀ P, φ P ≠ 0 := fun P => by rw [hφ]; exact Complex.exp_ne_zero _
  refine ⟨Metric.ball b₀ r₂, Metric.isOpen_ball, Metric.mem_ball_self hr₂,
    (hb2.trans hb1).trans hball, (convex_ball b₀ r₂).isPreconnected, s, ?_, ?_, φ, hφd,
    fun P _ => hφ0 P, ?_⟩
  · intro l _
    rw [hs]
    exact continuousOn_finset_sum _ fun k _ => continuousOn_const.mul (hs'c k)
  · intro l _ l' _ b _
    exact hsadd l l' b

  obtain ⟨j, hj⟩ : ∃ j : Fl g → Pt E g → ℂ, j = fun l P =>
      φ (transl τ l P) * Complex.exp (2 * π * Complex.I * s l P.1) * (φ P)⁻¹ := ⟨_, rfl⟩
  have hjc : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov (Metric.ball b₀ r₂) g,
      j (l + l') P = j l (transl τ l' P) * j l' P := by
    intro l _ l' _ P _
    rw [hj]
    dsimp only
    rw [transl_transl, hsadd, mul_add, Complex.exp_add]
    have : (transl τ l' P).1 = P.1 := rfl
    rw [this]
    field_simp [hφ0]
  have hj0 : ∀ l ∈ stdLat g, ∀ P ∈ cov (Metric.ball b₀ r₂) g, j l P ≠ 0 := by
    intro l _ P _
    rw [hj]
    exact mul_ne_zero (mul_ne_zero (hφ0 _) (Complex.exp_ne_zero _)) (inv_ne_zero (hφ0 _))
  have hgen : ∀ i, ∀ P ∈ cov (Metric.ball b₀ r₂) g, j (Pi.single i 1) P = u (Pi.single i 1) P := by
    intro i P hP
    rw [hae i P (h10 (h21 hP)), hj]
    dsimp only
    rw [mul_inv_eq_iff_eq_mul₀ (hφ0 P)]
    rcases i with k | k
    · have hsk : s (Pi.single (Sum.inl k) 1) P.1 = s' k P.1 := by
        rw [hs]
        dsimp only
        rw [Finset.sum_eq_single k (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
        simp
      have h2 := hψ₂ k P hP
      rw [ha'] at h2
      dsimp only at h2
      rw [hsk, hφ]
      dsimp only
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      linear_combination (2 * π * Complex.I) * h2
    · have hsk : s (Pi.single (Sum.inr k) 1) P.1 = 0 := by
        rw [hs]
        simp [Pi.single_apply]
      rw [hsk, transl_inr]
      have h1 := hψ₁ k P (h21 hP)
      have h2 := hψ₂per k P hP
      rw [hφ]
      dsimp only
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      linear_combination (2 * π * Complex.I) * (h1 + h2)
  have hu' : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov (Metric.ball b₀ r₂) g,
      u (l + l') P = u l (transl τ l' P) * u l' P := fun l hl l' hl' P hP =>
    hu.2 l hl l' hl' P (hcov0 (h10 (h21 hP)))
  have hu0 : ∀ l ∈ stdLat g, ∀ P ∈ cov (Metric.ball b₀ r₂) g, u l P ≠ 0 := fun l hl P hP =>
    (hu.1 l hl).2 P (hcov0 (h10 (h21 hP)))
  have heq := eq_of_eq_on_basis j u hjc hj0 hu' hu0 hgen
  intro l hl P hP
  have h := heq l hl P hP
  rw [hj] at h
  dsimp only at h
  rw [← h]
  field_simp [hφ0]

end GlobalTheory.FactorDegreeZero
