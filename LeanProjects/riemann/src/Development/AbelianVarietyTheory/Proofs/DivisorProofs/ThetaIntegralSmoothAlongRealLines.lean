import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineActionDerivativePureTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtIntegralDominatedFamilyStatement

noncomputable section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThKDer

theorem lineA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • W.J.map σ)), IsRealLine σ (c • W.J.map σ) γ →
    ∃ γL ∈ Lines σ W, ∀ t : ℝ, (toGAd hσ W.J hc).symm (γ t) = γL (Multiplicative.ofAdd t) := GlobalTheory.T.real_line_corresponds_to_line

theorem kerDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ g h,
    HasDerivAt (fun s : ℝ => theta om (pure f φ) g (h * γ (Multiplicative.ofAdd s))) (theta om (pure f₁ φ) g h) 0 := GlobalTheory.T.line_action_derivative_pure_tensor

theorem derivIntegral : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F F₁ F₂ : ℝ → α → ℂ) (B : ℝ),
    (∀ x s, HasDerivAt (fun r => F r x) (F₁ s x) s) → (∀ x s, HasDerivAt (fun r => F₁ r x) (F₂ s x) s) →
    (∀ s, Integrable (F s) μ) → (∀ s, Integrable (F₁ s) μ) → (∀ s, Integrable (F₂ s) μ) →
    (∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₁ s x‖ ∂μ ≤ B) → (∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₂ s x‖ ∂μ ≤ B) →
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F₁ 0 x ∂μ) 0 := GlobalTheory.T.has_deriv_at_integral_dominated_family

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : GlobalTheory.ThK.PolData B M ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)

section Triple

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem theta_add (hT : IsTriple B G X om om') {Φ Ψ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')))
    (hΨ : Ψ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) (g h) :
    theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  have hs := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  simp only [theta, map_add]
  exact GlobalTheory.WeilM.thetaSum_add F (hs.pres _ _ hΦ) (hs.pres _ _ hΨ)

theorem theta_smul (c : ℂ) (Φ) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul]
  exact GlobalTheory.WeilM.thetaSum_smul F c _

theorem theta_zero (g h) : theta om 0 g h = 0 := by
  simp [theta, GlobalTheory.WeilM.thetaSum]

theorem exists_der (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ g h,
      HasDerivAt (fun s : ℝ => theta om Φ g (h * γ (Multiplicative.ofAdd s))) (theta om Φ₁ g h) 0 := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G X om om' hT γ hγ
  have hle := polData_le (B := B) hT.geo.hM
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
    exact ⟨pure (δ f) φ, Submodule.subset_span ⟨δ f, (hδ f hf).1, φ, hSB, hvac, rfl⟩,
      fun g h => kerDer F E σ B a a' G X om om' hKP hT γ hγ f hf (δ f) (hδ f hf).2 φ hSB hvac g h⟩
  | zero =>
    exact ⟨0, zero_mem _, fun g h => by simpa [theta_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x₁, hx₁, ex⟩ := ihx
    obtain ⟨y₁, hy₁, ey⟩ := ihy
    refine ⟨x₁ + y₁, add_mem hx₁ hy₁, fun g h => ?_⟩
    rw [theta_add hT (hle hx₁) (hle hy₁)]
    simp only [theta_add hT (hle hx) (hle hy)]
    exact (ex g h).add (ey g h)
  | smul c x hx ihx =>
    obtain ⟨x₁, hx₁, ex⟩ := ihx
    refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, fun g h => ?_⟩
    simp only [theta_smul]
    exact (ex g h).const_mul c

theorem hasDerivAt_shift {γ : Multiplicative ℝ →* UA σ G.W.J} {Φ Φ₁}
    (hd : ∀ g h, HasDerivAt (fun s : ℝ => theta om Φ g (h * γ (Multiplicative.ofAdd s))) (theta om Φ₁ g h) 0)
    (g h) (s : ℝ) :
    HasDerivAt (fun r : ℝ => theta om Φ g (h * γ (Multiplicative.ofAdd r)))
      (theta om Φ₁ g (h * γ (Multiplicative.ofAdd s))) s := by
  have e0 : HasDerivAt (fun u : ℝ => theta om Φ g (h * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd u)))
      (theta om Φ₁ g (h * γ (Multiplicative.ofAdd s))) (s - s) := by
    rw [sub_self]; exact hd g _
  have e := e0.comp_sub_const s s
  refine e.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  show theta om Φ g (h * γ (Multiplicative.ofAdd r)) =
    theta om Φ g (h * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (r - s)))
  rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]

end Triple

section Triple2

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem conv_pol (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') :
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.Conv om Ψ ∧
      ∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in G.M.dom, ‖theta om Ψ g h‖ ∂G.M.μ ≤ C * (ht h : ℝ) ^ k := by
  intro Ψ hΨ
  have hineq : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    left
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    omega
  exact (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Inhab.pairV hT) hineq).1 Ψ (polData_le hT.geo.hM hΨ)

end Triple2

theorem ht_line_bdd {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) :
    ∃ Bd : ℝ, ∀ s ∈ Set.Icc (-1 : ℝ) 1, (ht (γ (Multiplicative.ofAdd s)) : ℝ) ≤ Bd := by
  have hc : Continuous fun s : ℝ => (ht (γ (Multiplicative.ofAdd s)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp
      (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, fun s hs => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC s hs)⟩

section Triple3

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem hasDerivAt_I (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ : Multiplicative ℝ →* UA σ G.W.J}
    (hγ : γ ∈ Lines σ G.W) {Φ₀ Φ₁ Φ₂} (h0 : Φ₀ ∈ GlobalTheory.ThK.PolData B G.M) (h1 : Φ₁ ∈ GlobalTheory.ThK.PolData B G.M)
    (h2 : Φ₂ ∈ GlobalTheory.ThK.PolData B G.M)
    (d1 : ∀ g h, HasDerivAt (fun s : ℝ => theta om Φ₀ g (h * γ (Multiplicative.ofAdd s))) (theta om Φ₁ g h) 0)
    (d2 : ∀ g h, HasDerivAt (fun s : ℝ => theta om Φ₁ g (h * γ (Multiplicative.ofAdd s))) (theta om Φ₂ g h) 0)
    (h : UA σ G.W.J) :
    HasDerivAt (fun s : ℝ => G.M.I om Φ₀ (h * γ (Multiplicative.ofAdd s))) (G.M.I om Φ₁ h) 0 := by
  obtain ⟨c0, -⟩ := conv_pol hKP hT Φ₀ h0
  obtain ⟨c1, C1, k1, b1⟩ := conv_pol hKP hT Φ₁ h1
  obtain ⟨c2, C2, k2, b2⟩ := conv_pol hKP hT Φ₂ h2
  obtain ⟨Bd, hBd⟩ := ht_line_bdd hγ
  set Y : ℝ := (ht h : ℝ) * Bd with hYdef
  have hY : ∀ s ∈ Set.Icc (-1 : ℝ) 1, (ht (h * γ (Multiplicative.ofAdd s)) : ℝ) ≤ Y := fun s hs => by
    have e := heightGL_mul_le F h.1 (γ (Multiplicative.ofAdd s)).1
    calc (ht (h * γ (Multiplicative.ofAdd s)) : ℝ) ≤ (ht h : ℝ) * ht (γ (Multiplicative.ofAdd s)) := by
          exact_mod_cast e
      _ ≤ Y := mul_le_mul_of_nonneg_left (hBd s hs) (NNReal.coe_nonneg _)
  have hY0 : 0 ≤ Y := (NNReal.coe_nonneg _).trans (hY 0 ⟨by norm_num, by norm_num⟩)
  have bnd : ∀ (C : ℝ) (k : ℕ) (Ψ : (Fin a × Fin (a + a') → AF F) → ℂ),
      (∀ h', ∫ g in G.M.dom, ‖theta om Ψ g h'‖ ∂G.M.μ ≤ C * (ht h' : ℝ) ^ k) →
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ g, ‖theta om Ψ g (h * γ (Multiplicative.ofAdd s))‖ ∂(G.M.μ.restrict G.M.dom) ≤
        |C| * Y ^ k := fun C k Ψ hb s hs =>
    (hb _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) k)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hY s hs) k) (abs_nonneg C)))
  have key := derivIntegral (G.M.μ.restrict G.M.dom)
    (fun s g => theta om Φ₀ g (h * γ (Multiplicative.ofAdd s)))
    (fun s g => theta om Φ₁ g (h * γ (Multiplicative.ofAdd s)))
    (fun s g => theta om Φ₂ g (h * γ (Multiplicative.ofAdd s)))
    (|C1| * Y ^ k1 + |C2| * Y ^ k2)
    (fun g s => hasDerivAt_shift d1 g h s) (fun g s => hasDerivAt_shift d2 g h s)
    (fun s => c0 _) (fun s => c1 _) (fun s => c2 _)
    (fun s hs => (bnd C1 k1 Φ₁ b1 s hs).trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (pow_nonneg hY0 _))))
    (fun s hs => (bnd C2 k2 Φ₂ b2 s hs).trans (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (pow_nonneg hY0 _))))
  simpa [Model.I] using key

end Triple3

theorem lineDer_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ : ℝ → GAd σ (c • G.W.J.map σ), IsRealLine σ (c • G.W.J.map σ) γ →
      ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, lineDer γ (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
        fun x => G.M.I om Φ₁ ((toGAd hσ G.W.J hc).symm x) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ Φ hΦ γ hγ
  obtain ⟨γL, hγL, eγ⟩ := lineA F E σ hσ hT.base.cm G.W c hc γ hγ
  obtain ⟨Φ₁, h1, d1⟩ := exists_der hKP hT hγL Φ hΦ
  obtain ⟨Φ₂, h2, d2⟩ := exists_der hKP hT hγL Φ₁ h1
  refine ⟨Φ₁, h1, funext fun x => ?_⟩
  have e : (fun t => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (x * γ t))) =
      fun t => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x * γL (Multiplicative.ofAdd t)) :=
    funext fun t => by rw [map_mul, eγ]
  show deriv (fun t => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (x * γ t))) 0 = _
  rw [e]
  exact (hasDerivAt_I hKP hT hγL hΦ h1 h2 d1 d2 _).deriv

end GlobalTheory.ThKDer
