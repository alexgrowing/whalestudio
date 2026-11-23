import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivarianceStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.Local

theorem eventually_eq_zero_of_fixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (σ : E → E)
    (hadd : ∀ x y, σ (x + y) = σ x + σ y) (hsmul : ∀ (c : ℂ) x, σ (c • x) = star c • σ x)
    (hinv : ∀ x, σ (σ x) = x) (hcont : Continuous σ) (x₀ : E) (hx₀ : σ x₀ = x₀) (f : E → F)
    (hf : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ f x ∧ (σ x = x → f x = 0)) :
    ∀ᶠ x in 𝓝 x₀, f x = 0 := by
  let u : E → E := fun x => (1 / 2 : ℂ) • (x + σ x)
  let v : E → E := fun x => (-Complex.I / 2 : ℂ) • x + (Complex.I / 2 : ℂ) • σ x
  have hu : ∀ x, σ (u x) = u x := by
    intro x
    simp only [u, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have hv : ∀ x, σ (v x) = v x := by
    intro x
    simp only [v, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have huv : ∀ x, u x + Complex.I • v x = x := by
    intro x
    simp only [u, v]
    match_scalars <;> (ring_nf; try simp) <;> norm_num
  have hG : Continuous fun p : E × ℂ => u p.1 + p.2 • v p.1 := by
    simp only [u, v]; fun_prop
  have h0 : ∀ t : ℂ, u x₀ + t • v x₀ = x₀ := by
    intro t
    simp only [u, v, hx₀]
    match_scalars; ring
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Metric.closedBall (0 : ℂ) 2,
      DifferentiableAt ℂ f (u x + t • v x) ∧ (σ (u x + t • v x) = u x + t • v x → f (u x + t • v x) = 0) := by
    apply (isCompact_closedBall (0 : ℂ) 2).eventually_forall_of_forall_eventually
    intro t _
    have := hG.tendsto (x₀, t)
    simp only [h0] at this
    exact this.eventually hf
  filter_upwards [htube] with x hx
  have hd : DifferentiableOn ℂ (fun t : ℂ => f (u x + t • v x)) (Metric.ball 0 2) := by
    intro t ht
    exact ((hx t (Metric.ball_subset_closedBall ht)).1.comp t (by fun_prop)).differentiableWithinAt
  have hfr : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (u x + t • v x) = 0 := by
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    refine ht.frequently (Eventually.frequently ?_)
    have hb : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ Metric.closedBall (0 : ℝ) 2 :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 two_pos)
    filter_upwards [hb] with s hs
    refine (hx s (by simpa using hs)).2 ?_
    rw [hadd, hu, hsmul, hv]; simp
  have := (hd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (Metric.mem_ball_self two_pos) hfr
    (show Complex.I ∈ Metric.ball (0 : ℂ) 2 by simp)
  simpa [huv] using this

theorem differentiableAt_of_coef {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (f : E → (W →L[ℂ] W)) (x : E)
    (hf : ∀ u v : W, DifferentiableAt ℂ (fun y => ⟪u, f y v⟫_ℂ) x) : DifferentiableAt ℂ f x := by
  let b := stdOrthonormalBasis ℂ W
  have e : f = fun y => ∑ i, ∑ j, ⟪b i, f y (b j)⟫_ℂ • (innerSL ℂ (b j)).smulRight (b i) := by
    funext y
    ext v
    conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' (f y _)]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Finset.sum_smul, smul_smul]
    simp only [mul_comm]
  rw [e]
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  exact (hf _ _).smul_const _

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

def prJ (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (a + Jm ε * a * Jm ε)

theorem prJ_comm (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε a * Jm ε = Jm ε * prJ ε a := by
  simp only [prJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, add_comm]

theorem prJ_of_comm {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (h : a * Jm ε = Jm ε * a) :
    prJ ε a = a := by
  rw [prJ, ← h, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  match_scalars; norm_num

theorem prJ_one (ε : Fin n → Bool) : prJ ε 1 = 1 := prJ_of_comm (by simp)

theorem prJ_conjTranspose (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε aᴴ = (prJ ε a)ᴴ := by
  simp [prJ, Jm_conjTranspose, Matrix.mul_assoc]

theorem differentiable_prJ (ε : Fin n → Bool) : Differentiable ℂ (prJ ε) := by
  unfold prJ; fun_prop

theorem eventually_isUnit : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), IsUnit a :=
  Units.isOpen.mem_nhds isUnit_one

theorem eventually_prJ_mem (ε : Fin n → Bool) : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), prJ ε a ∈ KC ε := by
  have := ((differentiable_prJ ε).continuous.tendsto' 1 1 (prJ_one ε)).eventually eventually_isUnit
  filter_upwards [this] with a ha
  exact ⟨ha, prJ_comm ε a⟩

theorem posDef_mul_conjTranspose {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsUnit c) : (c * cᴴ).PosDef := by
  rw [(Matrix.posSemidef_self_mul_conjTranspose c).posDef_iff_isUnit]
  exact hc.mul (by simpa [Matrix.star_eq_conjTranspose] using hc.star)

theorem posDef_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by simp [hX]
  have e : X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • X := by match_scalars; norm_num
  have := posDef_mul_conjTranspose (Matrix.isUnit_exp ((1 / 2 : ℂ) • X))
  rwa [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e] at this

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_differentiableAt_tau {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) :
    ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (fun y => τ (prJ ε y)) a := by
  haveI := hτ.1
  filter_upwards [(eventually_prJ_mem ε).eventually_nhds] with a ha
  refine differentiableAt_of_coef _ _ fun u v => ?_
  have h : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ y v⟫_ℂ) (KC ε) := hτ.2.2.1 u v
  have h2 : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ (prJ ε y) v⟫_ℂ)
      {y | prJ ε y ∈ KC ε} :=
    h.comp (differentiable_prJ ε).differentiableOn fun y hy => hy
  exact h2.differentiableAt ha

theorem eventually_ps_mul (hB : PsBasic) (hE : PsEquiv) (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) :
    ∀ᶠ x : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) in 𝓝 ((1, 1), (1, 1)),
      ps ε lam τ w (prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1) -
        τ (prJ ε x.1.1) * ps ε lam τ w (x.1.2 * x.2.2) * τ (prJ ε x.2.1) = 0 := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨hopen, hpos, hdiff, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hdiff' : DifferentiableOn ℂ (ps ε lam τ w) (U1 ε) := hdiff
  have hps : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
    exact hdiff'.differentiableAt (hopen'.mem_nhds hz)
  have hP := differentiable_prJ ε
  refine eventually_eq_zero_of_fixed (fun x => ((x.2.1ᴴ, x.2.2ᴴ), (x.1.1ᴴ, x.1.2ᴴ))) ?_ ?_ ?_ ?_ _ ?_ _ ?_
  · intro x y; simp
  · intro c x; simp
  · intro x; simp
  · fun_prop
  · simp
  · let E := (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    have d1 : Differentiable ℂ fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1 := by
      fun_prop
    have d2 : Differentiable ℂ fun x : E => x.1.2 * x.2.2 := by fun_prop
    have d3 : Differentiable ℂ fun x : E => x.1.1 := by fun_prop
    have d4 : Differentiable ℂ fun x : E => x.2.1 := by fun_prop
    have d5 : Differentiable ℂ fun x : E => x.1.2 := by fun_prop
    filter_upwards [(d1.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp [prJ_one])).eventually hps,
      (d2.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp)).eventually hps,
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d4.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_prJ_mem ε),
      (d5.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually eventually_isUnit] with x h1 h2 h3 h4 h5 h6
    have k1 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1)
      x h1 (d1 x)
    have k2 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => x.1.2 * x.2.2) x h2 (d2 x)
    have k3 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.1.1) x h3 (d3 x)
    have k4 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.2.1) x h4 (d4 x)
    refine ⟨k1.sub ((k3.mul k2).mul k4), ?_⟩
    intro hx
    have e1 : x.2.1 = x.1.1ᴴ := (congrArg (fun y => y.2.1) hx).symm
    have e2 : x.2.2 = x.1.2ᴴ := (congrArg (fun y => y.2.2) hx).symm
    rw [e1, e2, prJ_conjTranspose, hE n ε lam W τ w hl hτ _ _ (posDef_mul_conjTranspose h6) h5, sub_eq_zero]
    rfl

theorem psLocal_of (hB : PsBasic) (hE : PsEquiv) : PsLocal := by
  intro n ε lam W _ _ τ w hl hτ
  obtain ⟨hopen, hpos, -, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hu1 : umat (1 : UJ ε) = 1 := rfl
  obtain ⟨L, hLc, hL⟩ := (polar_decomposition_holds n ε).2.2
  have hdec : ∀ g : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp (-L g) * NormedSpace.exp (L g) = g := by
    intro g
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have h1U : inUJ ε 1 := by simp [inUJ]
  have hL1 : L 1 = 0 := by
    refine ((polar_decomposition_holds n ε).2.1 _ 1 _ 0 (hL 1 h1U).2 ⟨one_mem _, by simp⟩ (hL 1 h1U).1
      (by simp [inP, inG]) ?_).2
    rw [hdec]; simp
  have hLc' : Continuous fun g : UJ ε => L (umat g) := hLc.comp_continuous hu fun g => g.2
  have hexp : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have hc : Continuous fun g : UJ ε =>
      (((umat g * NormedSpace.exp (-L (umat g)), NormedSpace.exp (L (umat g))), (1, 1)) :
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
          (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    ((hu.mul (hexp.comp hLc'.neg)).prodMk (hexp.comp hLc')).prodMk continuous_const
  filter_upwards [(hu.tendsto' 1 1 hu1).eventually (hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)),
    (hc.tendsto' 1 ((1, 1), (1, 1)) (by simp [hu1, hL1])).eventually (eventually_ps_mul hB hE hl hτ)]
    with g hg1 hg2
  refine ⟨hg1, ?_⟩
  obtain ⟨hX, hk⟩ := hL (umat g) g.2
  simp only [prJ_one, prJ_of_comm hk.2, mul_one, hτ.2.1.1, hdec, sub_eq_zero] at hg2
  rw [hg2]
  conv_lhs => rw [← hdec (umat g)]
  exact Psi_unitary_mul ε lam τ w hk.1 (posDef_exp (hermitian_of_mem_hermitian_part hX))

end GlobalTheory.Dec.Local

theorem GlobalTheory.Dec.psLocal : PsLocal := GlobalTheory.Dec.Local.psLocal_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
