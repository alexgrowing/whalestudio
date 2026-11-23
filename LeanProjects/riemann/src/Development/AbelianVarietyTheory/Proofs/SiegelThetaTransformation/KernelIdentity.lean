import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivConstMul
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpecStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraphStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNormStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeightStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwdStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolutionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLtStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace KernSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}

theorem isSB_wG (γ : GL (Fin r) E) (φ : TF n g) : IsSB (wG X bas idx γ φ) := by
  unfold wG
  split_ifs with h
  · exact h.choose_spec.1
  · exact isSB_zero

theorem ip_smul_right {φ ψ : TF n g} (hφ : IsSB φ) (hψ : IsSB ψ) (c : ℂ) :
    ip φ (c • ψ) = ip φ ψ * conj c := by
  obtain ⟨-, -, -, hcψ, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) ψ ψ hψ hψ
  obtain ⟨-, -, hprod, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) φ _ hφ hcψ
  obtain ⟨-, -, -, -, -, hsmul, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hprod hprod
  have e : (fun x => φ x * conj ((c • ψ) x)) = conj c • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  unfold ip
  rw [e, hsmul, mul_comm]
  rfl

theorem hasSum_eis (hb : IsSympl X bas) (hn : Even n) (h4 : 4 * r < n) {M : ℕ}
    {Δ : Subgroup (GL (Fin r) E)} {𝓛 : Set (Lt E r)} {Φ : Lt E r → Lt E n → TF n g}
    {μ : GL (Fin r) E → Lt E r → ℂ} (hS : IsSystem X bas idx M Δ 𝓛 Φ μ) {a : ℂ}
    (ha : ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂)
    {L₁ L₂ : Lt E r} (h₁ : L₁ ∈ 𝓛) (h₂ : L₂ ∈ 𝓛) {x₁ x₂ : Frame X.Ψ r} (hx₁ : x₁ ∈ X.dom)
    (hx₂ : x₂ ∈ X.dom) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) (z w : Fin n → Fin g → ℂ) :
    HasSum (fun γ : Δ => a * ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ) * conj (μ γ L₂) *
        kZero X idx x₁ (lact γ x₂) z w)
      (kZero X idx x₁ x₂ z w * eis X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)) := by
  set φ₁ := Φ L₁ Λ with hφ₁def
  set φ₂ := Φ L₂ Λ with hφ₂def
  have hφ₁ : IsSB φ₁ := hS.sb L₁ h₁ Λ hΛ
  have hφ₂ : IsSB φ₂ := hS.sb L₂ h₂ Λ hΛ
  have hψ : IsSB (dbl X bas idx φ₁ φ₂) := (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hb hn φ₁ φ₂ hφ₁ hφ₂).1
  obtain ⟨hT, hZ, -⟩ := GlobalTheory.SW.dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂
  have hsum := (GlobalTheory.SW.eis_automorphy_linear E X.Ψ hT n r hn h4 _ hψ _ hZ).1
    (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)
  have hU := (hsum.of_norm.hasSum).mul_left (kZero X idx x₁ x₂ z w)
  have hun1 : IsUn X (1 : GL (Fin r) E) := by
    intro u v
    simp
  let lagOf : Δ → Lag E r := fun γ =>
    ⟨botSpan (iota X 1 γ), iota X 1 γ, DblPair.iota_mem X hun1 (hS.un γ γ.2), rfl⟩
  have hinj : Function.Injective lagOf := by
    intro γ γ' h
    have h' : botSpan (iota X 1 (γ : GL (Fin r) E)) = botSpan (iota X 1 (γ' : GL (Fin r) E)) :=
      congrArg Subtype.val h
    exact Subtype.ext ((GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic E r X).1 γ γ' (hS.un γ γ.2) (hS.un γ' γ'.2) h')
  have hterm : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ U : Lag E r, botSpan (iota X 1 γ) = U.1 →
      kZero X idx x₁ x₂ z w * eisTerm X.Ψ U.2.choose (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w) =
      a * ip φ₁ (wG X bas idx γ φ₂) * kZero X idx x₁ (lact γ x₂) z w := by
    intro γ hγ U hUγ
    have e1 := (GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E X.Ψ hT n r hn _ hψ).2 U.2.choose U.2.choose_spec.1 (iota X 1 γ)
      (DblPair.iota_mem X hun1 hγ) (U.2.choose_spec.2.trans hUγ.symm) _ hZ
      (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)
    have e2 := GlobalTheory.T.eisensteinSeries_term_unitary_graph E r X g bas idx n hb hn γ hγ φ₁ φ₂ hφ₁ hφ₂ x₁ hx₁ x₂ hx₂ z w
    have e3 := ha φ₁ _ hφ₁ (isSB_wG (X := X) (bas := bas) (idx := idx) γ φ₂)
    rw [e1, e2, e3]
  have hzero : ∀ U ∉ Set.range lagOf, kZero X idx x₁ x₂ z w * eisTerm X.Ψ U.2.choose
      (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w) = 0 := by
    intro U hU'
    rcases (GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic E r X).2 U with ⟨γ, hγ, hUγ⟩ | ⟨ξ, hξ0, hξ, hmem⟩
    · have hγΔ : γ ∉ Δ := fun hΔ => hU' ⟨⟨γ, hΔ⟩, Subtype.ext hUγ⟩
      have e1 := hterm γ hγ U hUγ
      have e2 := hS.supp γ hγ hγΔ L₁ h₁ L₂ h₂ Λ hΛ
      rw [e1, e2]
      ring
    · have hw : weil X.Ψ U.2.choose (dbl X bas idx φ₁ φ₂) 0 = 0 :=
        GlobalTheory.T.weil_doubledTestFunction_zero_eq_zero E r X g bas idx n hb hn φ₁ φ₂ hφ₁ hφ₂ ξ (hS.cusp ξ hξ0 hξ L₁ h₁ Λ hΛ)
          U.2.choose U.2.choose_spec.1 (by rw [U.2.choose_spec.2]; exact hmem)
      unfold eisTerm
      rw [hw]
      ring
  have hmain := (hinj.hasSum_iff hzero).2 hU
  unfold eis
  convert hmain using 1
  funext γ
  have hΦ' : IsSB (Φ (mapL γ L₂) Λ) := hS.sb _ (hS.stab γ γ.2 L₂ h₂) Λ hΛ
  have e1 := hterm γ (hS.un γ γ.2) (lagOf γ) rfl
  have e2 := (hS.mu γ γ.2 L₂ h₂).2 Λ hΛ
  have e3 := ip_smul_right hφ₁ hΦ' (μ γ L₂)
  simp only [Function.comp_apply]
  rw [e1, e2, e3]
  ring

end KernSum

private theorem analyticAt_mul_cexp_bilin_diag {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (A : ℂ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (p : V) :
    AnalyticAt ℂ (fun v => A * cexp (B v v)) p := by
  let B' : V →L[ℂ] V →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B)
  have h0 : AnalyticAt ℂ (fun v : V => (v, v)) p := analyticAt_id.prod analyticAt_id
  have h1 : AnalyticAt ℂ (fun v : V => B' v v) p := AnalyticAt.comp (g := fun x : V × V => B' x.1 x.2)
    (f := fun v : V => (v, v)) (B'.analyticAt_bilinear (p, p)) h0
  exact analyticAt_const.mul h1.cexp

private theorem analyticAt_and_hasSum_bd_of_hasSum_gaussian {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {σ : Type} (P Q : MvPolynomial σ ℂ) (u : σ → W) {ι : Type}
    (F : ι → W × W → ℂ) (S : W × W → ℂ) (A : ι → ℂ) (B : ι → (W × W) →ₗ[ℂ] (W × W) →ₗ[ℂ] ℂ)
    (hF : ∀ i p, F i p = A i * cexp (B i p p)) (hS : ∀ p, HasSum (fun i => F i p) (S p)) :
    (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun i => KernSum.bd P Q u (F i)) (KernSum.bd P Q u S) := by
  have hFa : ∀ i p, AnalyticAt ℂ (F i) p := by
    intro i p
    have e : F i = fun v => A i * cexp (B i v v) := funext (hF i)
    rw [e]
    exact analyticAt_mul_cexp_bilin_diag (A i) (B i) p
  refine KernSum.bd_hasSum P Q u hFa hS fun R => ?_
  have hsum : ∀ v, Summable fun i => A i * cexp (B i v v) := by
    intro v
    have e : (fun i => A i * cexp (B i v v)) = fun i => F i v := funext fun i => (hF i v).symm
    rw [e]
    exact (hS v).summable
  obtain ⟨v, hv, hle⟩ := KernSum.exists_majorant A B hsum R
  refine ⟨v, hv, fun i p hp => ?_⟩
  rw [hF i p]
  exact hle i p hp

private theorem analyticAt_mul_conj_comp_star_prod {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W] {f h : W → ℂ}
    (hf : ∀ p, AnalyticAt ℂ f p) (hh : ∀ p, AnalyticAt ℂ h p) (p : W × W) :
    AnalyticAt ℂ (fun q : W × W => f q.1 * conj (h (star q.2))) p := by
  have h1 : AnalyticAt ℂ (fun q : W × W => f q.1) p := (hf p.1).comp analyticAt_fst
  have h2 : AnalyticAt ℂ (fun q : W × W => conj (h (star q.2))) p :=
    (KernSum.analyticAt_conj hh p.2).comp analyticAt_snd
  exact h1.mul h2

private theorem bd_sum_prod_lemma_4 {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W] {σ : Type}
    (P : MvPolynomial σ ℂ) (u : σ → W) (hu : ∀ s, star (u s) = u s) {κ : Type} [Fintype κ]
    (wv : κ → ℂ) (f h : κ → W → ℂ) (hf : ∀ k p, AnalyticAt ℂ (f k) p)
    (hh : ∀ k p, AnalyticAt ℂ (h k) p) :
    (∀ p, AnalyticAt ℂ (fun q : W × W => ∑ k, wv k * (f k q.1 * conj (h k (star q.2)))) p) ∧
      KernSum.bd P (barP P) u (fun q : W × W => ∑ k, wv k * (f k q.1 * conj (h k (star q.2)))) =
        ∑ k, wv k * (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (f k) 0 *
          conj (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (h k) 0)) := by
  have hA : ∀ k p, AnalyticAt ℂ (fun q : W × W => wv k * (f k q.1 * conj (h k (star q.2)))) p :=
    fun k p => analyticAt_const.mul (analyticAt_mul_conj_comp_star_prod (hf k) (hh k) p)
  refine ⟨fun p => ?_, ?_⟩
  · have h1 := Finset.analyticAt_sum (𝕜 := ℂ) (Finset.univ : Finset κ) fun k _ => hA k p
    rw [Finset.sum_fn] at h1
    exact h1
  · rw [KernSum.bd_sum P (barP P) u Finset.univ fun k => hA k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [KernSum.bd_const_mul P (barP P) u (wv k) fun p => analyticAt_mul_conj_comp_star_prod (hf k) (hh k) p,
      KernSum.bd_prod P P u hu (hf k) (hh k)]

open KernSum in

theorem kernel_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * r < n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ a : ℂ, a ≠ 0 ∧ ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ), ∀ (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') → InvFam P → ∀ L₁ ∈ 𝓛, ∀ L₂ ∈ 𝓛, ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, HasSum (fun γ : Δ => a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂) * kern X hr idx P x₁ (lact γ x₂)) (classSum M (fun Λ => ∑ j, thP X hr bas idx (Φ L₁ Λ) (P j) x₁ * conj (thP X hr bas idx (Φ L₂ Λ) (P j) x₂))) := by
  intro E _ _ _ r X g q0 hr bas idx n hb hn h4 M Δ 𝓛 Φ μ hM hS
  obtain ⟨a, ha0, b, -, hab⟩ := GlobalTheory.T.doubledHermitianTestFunction_zero_and_norm E r X g bas idx n hb hn
  refine ⟨a, ha0, ?_⟩
  intro c c' m P hP hInv L₁ h₁ L₂ h₂ x₁ hx₁ x₂ hx₂
  have ha : ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂ :=
    fun φ₁ φ₂ e₁ e₂ => (hab φ₁ φ₂ e₁ e₂).1
  have hT : IsType X.Ψ := Base.isType_data X
  have : Fintype (Cls E n M) := @Fintype.ofFinite _ (finite_cls_and_stab E n M hM).1
  have hcs : ∀ f : Lt E n → ℂ, classSum M f =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * f (Quot.out cl).1 :=
    fun f => finsum_eq_sum_of_fintype _
  have hu : ∀ s : Harm.Var X.Ψ q0 X.p0 (Fin n), star (letterDir X hr idx s) = letterDir X hr idx s := by
    intro s
    funext k i
    unfold letterDir
    simp only [Pi.star_apply, Pi.single_apply]
    split_ifs
    · simp only [Pi.single_apply]
      split_ifs <;> simp
    · simp
  have hφ : ∀ (L : Lt E r), L ∈ 𝓛 → ∀ cl : Cls E n M, IsSB (Φ L (Quot.out cl).1) :=
    fun L hL cl => hS.sb L hL _ (Quot.out cl).2
  have hthA : ∀ (j : Fin m) (L : Lt E r), L ∈ 𝓛 → ∀ cl : Cls E n M, ∀ x ∈ X.dom, ∀ p,
      AnalyticAt ℂ (thA X bas idx (Φ L (Quot.out cl).1) x) p := by
    intro j L hL cl x hx p
    exact (GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight E r X g q0 hr bas idx n hb hn c c' _ (hφ L hL cl) (P j) (hP j)).2.2.2
      x hx p (Set.mem_univ p)
  have hq := fun γ : Δ => KernSum.kZero_quad (n := n) X idx x₁ (lact (γ : GL (Fin r) E) x₂)
  choose A B hAB using hq
  have hK0 : ∀ γ : Δ, ∀ p, AnalyticAt ℂ (fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) q.1 q.2) p := by
    intro γ p
    have e : (fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
        kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) q.1 q.2) = fun q => A γ * cexp (B γ q q) :=
      funext (hAB γ)
    rw [e]
    exact analyticAt_mul_cexp_bilin_diag (A γ) (B γ) p
  obtain ⟨S, hSd⟩ : ∃ S : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) → ℂ, ∀ p, S p =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * (kZero X idx x₁ x₂ p.1 p.2 *
        eis X.Ψ (dbl X bas idx (Φ L₁ (Quot.out cl).1) (Φ L₂ (Quot.out cl).1)) (dblZ X x₁ x₂)
          (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2)) := ⟨_, fun p => rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) → ℂ, ∀ p, T p =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) *
        (thA X bas idx (Φ L₁ (Quot.out cl).1) x₁ p.1 *
          conj (thA X bas idx (Φ L₂ (Quot.out cl).1) x₂ (star p.2))) := ⟨_, fun p => rfl⟩
  have hpt : ∀ p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ), HasSum (fun γ : Δ =>
      (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
        kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) (S p) := by
    intro p
    have h := hasSum_sum (s := (Finset.univ : Finset (Cls E n M))) fun cl _ =>
      (KernSum.hasSum_eis hb hn h4 hS ha h₁ h₂ hx₁ hx₂ (Quot.out cl).2 p.1 p.2).mul_left
        (wt M (Quot.out cl).1 : ℂ)
    have e : ∀ γ : Δ, (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) *
        conj (μ γ L₂)) * kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2 =
        ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * (a * ip (Φ L₁ (Quot.out cl).1)
          (Φ (mapL γ L₂) (Quot.out cl).1) * conj (μ γ L₂) *
            kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := by
      intro γ
      rw [hcs, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cl _ => ?_
      ring
    simp only [e]
    rw [hSd p]
    exact h
  have hHS : ∀ j, (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun γ : Δ =>
      KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) (fun p =>
        (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
          kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2))
      (KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S) := by
    intro j
    refine analyticAt_and_hasSum_bd_of_hasSum_gaussian (P j) (barP (P j)) (letterDir X hr idx) _ S
      (fun γ => (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) * A γ)
      B (fun γ p => ?_) hpt
    beta_reduce
    rw [hAB γ p]
    ring
  have eT : T = fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      ∑ cl : Cls E n M, (fun cl => (wt M (Quot.out cl).1 : ℂ)) cl *
        ((fun cl => thA X bas idx (Φ L₁ (Quot.out cl).1) x₁) cl q.1 *
          conj ((fun cl => thA X bas idx (Φ L₂ (Quot.out cl).1) x₂) cl (star q.2))) :=
    funext hTd
  have hTP := fun j : Fin m => bd_sum_prod_lemma_4 (P j) (letterDir X hr idx) hu
    (fun cl : Cls E n M => (wt M (Quot.out cl).1 : ℂ))
    (fun cl => thA X bas idx (Φ L₁ (Quot.out cl).1) x₁)
    (fun cl => thA X bas idx (Φ L₂ (Quot.out cl).1) x₂)
    (fun cl => hthA j L₁ h₁ cl x₁ hx₁) (fun cl => hthA j L₂ h₂ cl x₂ hx₂)
  have hTa : ∀ j : Fin m, ∀ p, AnalyticAt ℂ T p := by
    intro j p
    rw [eT]
    exact (hTP j).1 p
  have hTj : ∀ j : Fin m, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) *
        (thP X hr bas idx (Φ L₁ (Quot.out cl).1) (P j) x₁ *
          conj (thP X hr bas idx (Φ L₂ (Quot.out cl).1) (P j) x₂)) := by
    intro j
    rw [eT]
    exact (hTP j).2
  obtain ⟨R, hAdm⟩ := hS.adm L₁ h₁ L₂ h₂
  have hheat := GlobalTheory.T.isHeat_swd_of_adm E X.Ψ hT n r hn h4 M R _ hAdm
  have hsw : ∀ Z ∈ Hn X.Ψ r, swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) Z 0 0 = 0 :=
    fun Z hZ => GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt E X.Ψ hT n r hn h4 M R _ hAdm Z hZ
  have hrn : r ≤ n := by omega
  have h0 := GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution E r X g q0 hr idx n m P hrn hInv _ hheat hsw x₁ hx₁ x₂ hx₂
  have hTS : (fun p => T p + (-1) * S p) = fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      kZero X idx x₁ x₂ p.1 p.2 * swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ))
        (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2) := by
    funext p
    have e : swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2) = classSum M (fun Λ =>
          thH X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2)
            (dblz' X idx x₁ x₂ p.1 p.2) -
          eis X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2)
            (dblz' X idx x₁ x₂ p.1 p.2)) := rfl
    rw [hTd p, hSd p, e, hcs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun cl _ => ?_
    have hD := (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hb hn _ _ (hφ L₁ h₁ cl) (hφ L₂ h₂ cl)).2.1
      x₁ hx₁ x₂ hx₂ p.1 p.2
    have hst : star p.2 = fun k i => conj (p.2 k i) := rfl
    rw [hst, hD]
    ring
  have hsplit : ∀ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx)
      (fun p => T p + (-1) * S p) = KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T +
        (-1) * KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
    intro j
    have e1 := KernSum.bd_add (P j) (barP (P j)) (letterDir X hr idx) (hTa j)
      (fun p => (analyticAt_const.mul ((hHS j).1 p) : AnalyticAt ℂ (fun q => (-1 : ℂ) * S q) p))
    have e2 := KernSum.bd_const_mul (P j) (barP (P j)) (letterDir X hr idx) (-1) ((hHS j).1)
    rw [← e2]
    exact e1
  have hzero : ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx)
      (fun p => T p + (-1) * S p) = 0 := by
    rw [hTS]
    exact h0
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum] at hzero
  have hval : classSum M (fun Λ => ∑ j, thP X hr bas idx (Φ L₁ Λ) (P j) x₁ *
      conj (thP X hr bas idx (Φ L₂ Λ) (P j) x₂)) =
      ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
    have e : ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T =
        ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
      linear_combination hzero
    rw [← e, hcs]
    simp only [hTj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cl _ => ?_
    rw [Finset.mul_sum]
  have hfun : ∀ γ : Δ, a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) *
      conj (μ γ L₂) * kern X hr idx P x₁ (lact (γ : GL (Fin r) E) x₂) =
      ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) (fun p =>
        (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
          kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := by
    intro γ
    have e : kern X hr idx P x₁ (lact (γ : GL (Fin r) E) x₂) = ∑ j, KernSum.bd (P j)
        (barP (P j)) (letterDir X hr idx)
          (fun p => kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := rfl
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (KernSum.bd_const_mul (P j) (barP (P j)) (letterDir X hr idx) _ (hK0 γ)).symm
  simp only [hfun]
  rw [hval]
  exact hasSum_sum fun j _ => (hHS j).2

end GlobalTheory.SW
