import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineActionDerivativePureTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtIntegralDominatedFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingPositive

noncomputable section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

section Lie

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.WeilM GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.ThKDerSmall.exists_actsD_small (hPr : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'}
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ := by
  obtain ⟨hb, hg, hc, -, hw⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV'.sig w) (hg.hV'.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V'.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V'.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hPr hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hPr hD hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A C Φ _ X.α B.mα hb.cm hb.std fr hΦ hwp.1
    hc.expα
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M'.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  intro γ hγ f hf
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
  exact ⟨_, mem _, h2⟩

end Lie

namespace GlobalTheory.ThKDerSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lineA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • W.J.map σ)), IsRealLine σ (c • W.J.map σ) γ →
    ∃ γL ∈ Lines σ W, ∀ t : ℝ, (toGAd hσ W.J hc).symm (γ t) = γL (Multiplicative.ofAdd t) := GlobalTheory.T.real_line_corresponds_to_line

theorem polData_le {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : GlobalTheory.ThK.PolData B M ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem rest_pure {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {ψ : AddChar (AF F) ℂ} {M : Model σ X W}
    (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
  ⟨fun x z hz => GlobalTheory.ThKKernelLine.finprod_add_of_at φ x z hz,
    GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)⟩

section Triple

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem theta_add (hT : IsTriple B G X om om') {Φ Ψ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')))
    (hΨ : Ψ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a'))) (g h) :
    theta om' (Φ + Ψ) g h = theta om' Φ g h + theta om' Ψ g h := by
  have hs := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  simp only [theta, map_add]
  exact GlobalTheory.WeilM.thetaSum_add F (hs.pres _ _ hΦ) (hs.pres _ _ hΨ)

theorem theta_smul (c : ℂ) (Φ) (g h) : theta om' (c • Φ) g h = c * theta om' Φ g h := by
  simp only [theta, map_smul]
  exact GlobalTheory.WeilM.thetaSum_smul F c _

theorem theta_zero (g h) : theta om' 0 g h = 0 := by
  simp [theta, GlobalTheory.WeilM.thetaSum]

theorem exists_der_pol (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M', ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M',
      (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ g h, HasDerivAt (fun s : ℝ => theta om' Φ g (h * γ (Multiplicative.ofAdd s))) (theta om' Φ₁ g h) 0 := by
  have hle := polData_le (B := B) hT.geo.hM'
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
    obtain ⟨f₁, hf₁, hD⟩ := GlobalTheory.ThKDerSmall.exists_actsD_small hKP.base hT γ hγ f hf
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, hf₁, φ, hSB, hvac, rfl⟩, fun x => ?_, fun g h => ?_⟩
    · exact hD _ (rest_pure hT.geo.hM' f φ hSB hvac) x
    · exact GlobalTheory.ThKKernelLine.hasDerivAt_theta_pure hKP.base G.M' B.ψ _ _ om' hT.base.cm hT.base.std hT.geo.hM'
        hT.weil' hγ f f₁ hD φ hSB hvac g h
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_, fun g h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simpa [theta_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy ihx ihy =>
    obtain ⟨x₁, hx₁, px, ex⟩ := ihx
    obtain ⟨y₁, hy₁, py, ey⟩ := ihy
    refine ⟨x₁ + y₁, add_mem hx₁ hy₁, fun z => ?_, fun g h => ?_⟩
    · simp only [map_add, Pi.add_apply]
      exact (px z).add (py z)
    · rw [theta_add hT (hle hx₁) (hle hy₁)]
      simp only [theta_add hT (hle hx) (hle hy)]
      exact (ex g h).add (ey g h)
  | smul c x hx ihx =>
    obtain ⟨x₁, hx₁, px, ex⟩ := ihx
    refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, fun z => ?_, fun g h => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (px z).const_mul c
    · simp only [theta_smul]
      exact (ex g h).const_mul c

open scoped Classical in

theorem exists_der_so (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∃ Φ₁ ∈ G.M'.So B.ψ B.τ₁,
      ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hloc, rfl⟩ := hx
    obtain ⟨c, c', h0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hKP.base G.M' B.ψ _ _ om' hT.base.cm
      hT.base.std hT.weil' γ hγ f
    have hR := rest_pure hT.geo.hM' f φ hSB hvac
    refine ⟨pure c' φ, Submodule.subset_span ⟨c', φ, hSB, hvac, hloc, rfl⟩, fun x => ?_⟩
    have ev : Continuous fun s : SInf F (Fin a' × Fin (a + a')) => s (fun j => evI F (x j)) :=
      (continuous_eval_const (F := BoundedContinuousFunction (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin a' × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ).continuous
    have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j))
        (c' (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
      rw [slope_def_module, h0]
      simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    have h3 : (fun t : ℝ => c t (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j)) =
        fun t => om' (1, γ (Multiplicative.ofAdd t)) (pure f φ) x := by
      funext t
      show tens (evI F) (⇑(c t)) (fun x => ∏ᶠ v, φ v fun j => evFin F v (x j)) x =
        om' (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun j => evFin F v (x j))) x
      rw [hacts t _ hR]
    rw [h3] at h2
    exact h2
  | zero =>
    exact ⟨0, zero_mem _, fun x => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x₁, hx₁, px⟩ := ihx
    obtain ⟨y₁, hy₁, py⟩ := ihy
    refine ⟨x₁ + y₁, add_mem hx₁ hy₁, fun z => ?_⟩
    simp only [map_add, Pi.add_apply]
    exact (px z).add (py z)
  | smul c x hx ihx =>
    obtain ⟨x₁, hx₁, px⟩ := ihx
    refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, fun z => ?_⟩
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (px z).const_mul c

theorem exists_der (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ g h, HasDerivAt (fun s : ℝ => theta om' Φ g (h * γ (Multiplicative.ofAdd s))) (theta om' Φ₁ g h) 0 := by
  intro Φ hΦ
  obtain ⟨hP, hS⟩ := Submodule.mem_inf.1 hΦ
  obtain ⟨Φ₁, h1, p1, d1⟩ := exists_der_pol hKP hT hγ Φ hP
  obtain ⟨Φ₁', h1', p1'⟩ := exists_der_so hKP hT hγ Φ hS
  have e : Φ₁ = Φ₁' := funext fun x => (p1 x).unique (p1' x)
  exact ⟨Φ₁, Submodule.mem_inf.2 ⟨h1, e ▸ h1'⟩, d1⟩

theorem hasDerivAt_shift {γ : Multiplicative ℝ →* UA σ G.W.J} {Φ Φ₁}
    (hd : ∀ g h, HasDerivAt (fun s : ℝ => theta om' Φ g (h * γ (Multiplicative.ofAdd s))) (theta om' Φ₁ g h) 0)
    (g h) (s : ℝ) :
    HasDerivAt (fun r : ℝ => theta om' Φ g (h * γ (Multiplicative.ofAdd r)))
      (theta om' Φ₁ g (h * γ (Multiplicative.ofAdd s))) s := by
  have e0 : HasDerivAt (fun u : ℝ => theta om' Φ g (h * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd u)))
      (theta om' Φ₁ g (h * γ (Multiplicative.ofAdd s))) (s - s) := by
    rw [sub_self]; exact hd g _
  have e := e0.comp_sub_const s s
  refine e.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  show theta om' Φ g (h * γ (Multiplicative.ofAdd r)) =
    theta om' Φ g (h * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (r - s)))
  rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]

theorem so_bound (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') :
    ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, (∀ h, Integrable (fun g => theta om' Ψ g h) (G.M'.μ.restrict G.M'.dom)) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g, ‖theta om' Ψ g h‖ ∂(G.M'.μ.restrict G.M'.dom) ≤ C * (ht h : ℝ) ^ k := by
  intro Ψ hSo
  have hPair := GlobalTheory.ThKContSmall.isPair_small hT
  have hS : Ψ ∈ GlobalTheory.WeilM.schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Ψ hS
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hKP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Ψ hSo 0
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hKP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := isFiniteMeasure_restrict.2 hv.ne
  have hle : ∀ g h, ‖theta om' Ψ g h‖ ≤ C * (ht h : ℝ) ^ k := fun g h => by
    have h1 := hC g h
    rwa [pow_zero, mul_one] at h1
  have hint : ∀ h, Integrable (fun g => theta om' Ψ g h) (G.M'.μ.restrict G.M'.dom) := fun h =>
    (integrable_const (C * (ht h : ℝ) ^ k)).mono'
      (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => hle g h)
  refine ⟨hint, (G.M'.μ.restrict G.M'.dom).real Set.univ * C, k, fun h => ?_⟩
  calc ∫ g, ‖theta om' Ψ g h‖ ∂(G.M'.μ.restrict G.M'.dom)
      ≤ ∫ g, C * (ht h : ℝ) ^ k ∂(G.M'.μ.restrict G.M'.dom) :=
        integral_mono (hint h).norm (integrable_const _) fun g => hle g h
    _ = (G.M'.μ.restrict G.M'.dom).real Set.univ * C * (ht h : ℝ) ^ k := by
        rw [integral_const, smul_eq_mul, mul_assoc]

end Triple

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
    (hγ : γ ∈ Lines σ G.W) {Φ₀ Φ₁ Φ₂} (h0 : Φ₀ ∈ G.M'.So B.ψ B.τ₁) (h1 : Φ₁ ∈ G.M'.So B.ψ B.τ₁)
    (h2 : Φ₂ ∈ G.M'.So B.ψ B.τ₁)
    (d1 : ∀ g h, HasDerivAt (fun s : ℝ => theta om' Φ₀ g (h * γ (Multiplicative.ofAdd s))) (theta om' Φ₁ g h) 0)
    (d2 : ∀ g h, HasDerivAt (fun s : ℝ => theta om' Φ₁ g (h * γ (Multiplicative.ofAdd s))) (theta om' Φ₂ g h) 0)
    (h : UA σ G.W.J) :
    HasDerivAt (fun s : ℝ => G.M'.I om' Φ₀ (h * γ (Multiplicative.ofAdd s))) (G.M'.I om' Φ₁ h) 0 := by
  obtain ⟨c0, -⟩ := so_bound hKP hT Φ₀ h0
  obtain ⟨c1, C1, k1, b1⟩ := so_bound hKP hT Φ₁ h1
  obtain ⟨c2, C2, k2, b2⟩ := so_bound hKP hT Φ₂ h2
  obtain ⟨Bd, hBd⟩ := ht_line_bdd hγ
  set Y : ℝ := (ht h : ℝ) * Bd with hYdef
  have hY : ∀ s ∈ Set.Icc (-1 : ℝ) 1, (ht (h * γ (Multiplicative.ofAdd s)) : ℝ) ≤ Y := fun s hs => by
    have e := heightGL_mul_le F h.1 (γ (Multiplicative.ofAdd s)).1
    calc (ht (h * γ (Multiplicative.ofAdd s)) : ℝ) ≤ (ht h : ℝ) * ht (γ (Multiplicative.ofAdd s)) := by
          exact_mod_cast e
      _ ≤ Y := mul_le_mul_of_nonneg_left (hBd s hs) (NNReal.coe_nonneg _)
  have hY0 : 0 ≤ Y := (NNReal.coe_nonneg _).trans (hY 0 ⟨by norm_num, by norm_num⟩)
  have bnd : ∀ (C : ℝ) (k : ℕ) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ h', ∫ g, ‖theta om' Ψ g h'‖ ∂(G.M'.μ.restrict G.M'.dom) ≤ C * (ht h' : ℝ) ^ k) →
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ g, ‖theta om' Ψ g (h * γ (Multiplicative.ofAdd s))‖ ∂(G.M'.μ.restrict G.M'.dom) ≤
        |C| * Y ^ k := fun C k Ψ hb s hs =>
    (hb _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) k)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hY s hs) k) (abs_nonneg C)))
  have key := GlobalTheory.hasDerivAt_integral_of_integral_bounds (G.M'.μ.restrict G.M'.dom)
    (fun s g => theta om' Φ₀ g (h * γ (Multiplicative.ofAdd s)))
    (fun s g => theta om' Φ₁ g (h * γ (Multiplicative.ofAdd s)))
    (fun s g => theta om' Φ₂ g (h * γ (Multiplicative.ofAdd s)))
    (|C1| * Y ^ k1 + |C2| * Y ^ k2)
    (fun g s => hasDerivAt_shift d1 g h s) (fun g s => hasDerivAt_shift d2 g h s)
    (fun s => c0 _) (fun s => c1 _) (fun s => c2 _)
    (fun s hs => (bnd C1 k1 Φ₁ b1 s hs).trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (pow_nonneg hY0 _))))
    (fun s hs => (bnd C2 k2 Φ₂ b2 s hs).trans (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (pow_nonneg hY0 _))))
  simpa [Model.I] using key

end Triple3

theorem lineDer_thetaIntegral_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ γ : ℝ → GAd σ (c • G.W.J.map σ), IsRealLine σ (c • G.W.J.map σ) γ →
      ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, lineDer γ (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) =
        fun x => G.M'.I om' Φ₁ ((toGAd hσ G.W.J hc).symm x) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ Φ hΦ γ hγ
  obtain ⟨γL, hγL, eγ⟩ := lineA F E σ hσ hT.base.cm G.W c hc γ hγ
  obtain ⟨Φ₁, h1, d1⟩ := exists_der hKP hT hγL Φ hΦ
  obtain ⟨Φ₂, h2, d2⟩ := exists_der hKP hT hγL Φ₁ h1
  refine ⟨Φ₁, h1, funext fun x => ?_⟩
  have e : (fun t => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm (x * γ t))) =
      fun t => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x * γL (Multiplicative.ofAdd t)) :=
    funext fun t => by rw [map_mul, eγ]
  show deriv (fun t => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm (x * γ t))) 0 = _
  rw [e]
  exact (hasDerivAt_I hKP hT hγL (Submodule.mem_inf.1 hΦ).2 (Submodule.mem_inf.1 h1).2 (Submodule.mem_inf.1 h2).2
    d1 d2 _).deriv

end GlobalTheory.ThKDerSmall
