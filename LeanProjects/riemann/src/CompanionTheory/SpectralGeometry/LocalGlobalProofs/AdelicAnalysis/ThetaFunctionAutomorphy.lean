import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvarianceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhatStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicatorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussianStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticSetupInvariantUnderIsometryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicatorsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMatrixSymmetricPosdefImagStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianFourierTransformFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeCosetParametrizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeMembershipTraceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramTransposeDualTraceIdentityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicCharacterExponentialFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLatticeMeasureFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

section Linear

theorem sb_add {V : Type} [TopologicalSpace V] {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') : SB (φ + φ') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

theorem sb_smul {V : Type} [TopologicalSpace V] (c : ℂ) {φ : V → ℂ} (h : SB φ) : SB (c • φ) :=
  ⟨by
    have := h.1.comp (fun z => c * z)
    exact this, h.2.smul_left⟩

theorem sb_integrable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    {χ : V → V → ℂ} {μ : Measure V} (hV : NADual V χ μ) {φ : V → ℂ} (h : SB φ) (y : V) :
    Integrable (fun x => φ x * χ x y) μ := by
  obtain ⟨hT, _, _, _, hB, hH, _, _, hC, _⟩ := hV
  have hc : Continuous fun x => φ x * χ x y :=
    h.1.continuous.mul (hC.comp (by fun_prop : Continuous fun x : V => (x, y)))
  exact hc.integrable_of_hasCompactSupport h.2.mul_right

theorem fou_add {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    {χ : V → V → ℂ} {μ : Measure V} (hV : NADual V χ μ) {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') :
    fou χ μ (φ + φ') = fou χ μ φ + fou χ μ φ' := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_integrable hV h y) (sb_integrable hV h' y)

theorem fou_smul {V : Type} [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V) (c : ℂ)
    (φ : V → ℂ) : fou χ μ (c • φ) = c • fou χ μ φ := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

end Linear

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem thTerm_one (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (x : ι → F) :
    thTerm B ρ P 1 (fun _ => 1) φ τ x = φ (toA x) * gauss B ρ P τ (cur (emb ρ x)) := by
  simp only [thTerm, one_mulVec]
  rfl

theorem theta_add {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} {τ : InfinitePlace F → ℂ} {φ φ' : (ι → A F) → ℂ}
    (h : Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) φ τ x‖)
    (h' : Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) φ' τ x‖) :
    theta B ρ P 1 (fun _ => 1) (φ + φ') τ =
      theta B ρ P 1 (fun _ => 1) φ τ + theta B ρ P 1 (fun _ => 1) φ' τ := by
  unfold theta
  rw [← h.of_norm.tsum_add h'.of_norm]
  refine tsum_congr fun x => ?_
  simp only [thTerm, Pi.add_apply, add_mul]

theorem theta_smul (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (c : ℂ) (φ : (ι → A F) → ℂ) :
    theta B ρ P 1 (fun _ => 1) (c • φ) τ = c * theta B ρ P 1 (fun _ => 1) φ τ := by
  unfold theta
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [thTerm, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem orth_one (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    IsOrth B ρ 1 (fun _ => 1) := by
  simp [IsOrth]

theorem poisson_form [DecidableEq (InfinitePlace F)] {M : ℕ} {B : Matrix ι ι F}
    {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im)
    (g : Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ) (hg : g.det ≠ 0)
    (a : ι × InfinitePlace F → ℝ) (u : (ι × InfinitePlace F → ℤ) → ι × InfinitePlace F → ℝ)
    (hu : ∀ n, DM B ρ *ᵥ u n = (g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) :
    ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P τ (cur (a + g *ᵥ fun i => (n i : ℝ))) =
      ((|g.det|⁻¹ * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ : ℝ) : ℂ) * cG B ρ P τ *
        ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P (fun w => -(τ w)⁻¹) (cur (u n)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ (DM B ρ *ᵥ u n) : ℝ) : ℂ)) := by
  obtain ⟨hS, hP, hE⟩ := GlobalTheory.T.siegel_matrix_symmetric_posdef_imag F ι M B ρ P hQ τ hτ
  have hpl := GlobalTheory.T.poisson_summation_gaussian (ι × InfinitePlace F) (ZM B ρ P τ) hS hP g hg a
  dsimp only at hpl
  obtain ⟨-, -, h⟩ := hpl
  simp only [hE] at h
  have hs : ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have h0 : ((Algebra.norm ℚ B.det : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hQ.2.2.2.1)
    have : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.mpr (abs_pos.mpr h0)
    exact_mod_cast this.ne'
  have key : ∀ n : ι × InfinitePlace F → ℤ,
      (∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) *
          Complex.I * ((x ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ))) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) =
      (((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ * cG B ρ P τ) *
        (gauss B ρ P (fun w => -(τ w)⁻¹) (cur (u n)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ (DM B ρ *ᵥ u n) : ℝ) : ℂ))) := by
    intro n
    have hf := GlobalTheory.T.gaussian_fourier_transform_formula F ι M B ρ P hQ τ hτ (u n)
    rw [hu n] at hf
    rw [hu n, mul_assoc (_)⁻¹, ← mul_assoc (cG B ρ P τ), ← hf]
    field_simp
  rw [h, tsum_congr key, tsum_mul_left]
  push_cast
  ring

end Global

section Base

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem theta_indC [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (a : ι → F) (N : ℕ) (g : Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ)
    (e : (ι × InfinitePlace F → ℤ) → ι → F) (hi : Function.Injective e)
    (hr : ∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e)
    (he : ∀ n, emb ρ (e n) = emb ρ a + g *ᵥ fun p => (n p : ℝ)) :
    theta B ρ P 1 (fun _ => 1) (indC N a) τ =
      ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P τ (cur (emb ρ a + g *ᵥ fun i => (n i : ℝ))) := by
  unfold theta
  rw [← hi.tsum_eq]
  · refine tsum_congr fun n => ?_
    rw [thTerm_one, he n, indC, Set.indicator_of_mem, one_mul]
    exact (hr _).2 ⟨n, rfl⟩
  · intro x hx
    by_contra hc
    apply hx
    rw [thTerm_one, indC, Set.indicator_of_notMem, zero_mul]
    exact fun h => hc ((hr x).1 h)

theorem base [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)}
    (hl : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ)
    {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    (hV : NADual (ι → A F) (chiB ψ (Bf B)) (muF B lf)) (a : ι → F) {N : ℕ} (hN : 0 < N)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im) :
    cG B ρ P τ * theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) (indC N a))
      (fun w => -(τ w)⁻¹) = theta B ρ P 1 (fun _ => 1) (indC N a) τ := by
  classical
  obtain ⟨hT, -, -, hdet, hemb, -, -⟩ := id hQ
  obtain ⟨b⟩ := GlobalTheory.T.totally_real_integral_basis_exists F hT
  have hgd := GlobalTheory.T.lattice_matrix_determinant_formula F ι ρ hT hemb b N
  set g := gM (ι := ι) ρ (fun v => b v) N with hgdef
  have hdisc : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero F))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgd
    exact (pow_pos (mul_pos (pow_pos hNr _) hdisc) _).ne hgd
  obtain ⟨e, ei, er, ee⟩ := GlobalTheory.T.lattice_coset_parametrization F ι ρ b a N hN
  obtain ⟨e', he', es⟩ := GlobalTheory.T.dual_lattice_parametrization F ι B b N hdet hN
  have hu : ∀ n : ι × InfinitePlace F → ℤ, DM B ρ *ᵥ emb ρ (e' n) = (g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ) := by
    intro n
    have h2 := GlobalTheory.T.gram_transpose_dual_trace_identity F ι M B ρ P hQ (fun v => b v) N (e' n)
    have h3 : gᵀ *ᵥ (DM B ρ *ᵥ emb ρ (e' n)) = fun i => (n i : ℝ) := by
      rw [hgdef, h2]
      funext p
      have := he' n p.1 p.2
      rw [this]
      simp
    have hU : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
    rw [← h3, mulVec_mulVec, ← transpose_mul, mul_nonsing_inv _ hU, transpose_one, one_mulVec]
  have pf := poisson_form hQ hτ g hg (emb ρ a) (fun n => emb ρ (e' n)) hu
  have ei' : Function.Injective e' := by
    intro n n' h
    funext p
    have h3 := he' n p.1 p.2
    rw [h, he' n' p.1 p.2] at h3
    exact_mod_cast h3.symm
  have hfou : ∀ y : ι → F, fou (chiB ψ (Bf B)) (muF B lf) (indC N a) (toA y) =
      ((muF B lf (latN F ι N : Set (ι → A F))).toReal : ℂ) * chiB ψ (Bf B) (toA a) (toA y) *
        Set.indicator (perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F))) (fun _ => (1 : ℂ)) (toA y) :=
    fun y => GlobalTheory.T.fourier_transform_lattice_indicator _ _ _ hV (latN F ι N) (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).1 (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.1 (toA a) (toA y)
  have hperp : ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔
      y ∈ Set.range e' := by
    intro y
    rw [GlobalTheory.T.dual_lattice_membership_trace F ψ hψ ι B b N hN y]
    constructor
    · intro h
      exact es y h
    · rintro ⟨n, rfl⟩ i v
      exact ⟨n (i, v), he' n i v⟩
  have hL : theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) (indC N a))
      (fun w => -(τ w)⁻¹) = ((muF B lf (latN F ι N : Set (ι → A F))).toReal : ℂ) *
        ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P (fun w => -(τ w)⁻¹) (cur (emb ρ (e' n))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ (e' n)) : ℝ) : ℂ)) := by
    unfold theta
    rw [← ei'.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun n => ?_
      rw [thTerm_one, hfou, Set.indicator_of_mem ((hperp _).2 ⟨n, rfl⟩),
        GlobalTheory.T.adelic_character_exponential_formula F ψ hψ ι M B ρ P hQ a (e' n)]
      ring
    · intro x hx
      by_contra hc
      apply hx
      rw [thTerm_one, hfou, Set.indicator_of_notMem (fun h => hc ((hperp x).1 h))]
      simp
  have hmass := GlobalTheory.T.adelic_lattice_measure_formula F lf hl h1 ι B N hN
  rw [hL, theta_indC B ρ P τ a N g e ei er ee, pf, hmass, hgd]
  have hk : kap F = (Real.sqrt |(discr F : ℝ)|)⁻¹ := rfl
  rw [hk]
  push_cast
  simp only [mul_inv, mul_pow, inv_pow]
  ring

theorem core [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)}
    (hl : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ)
    {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    (hV : NADual (ι → A F) (chiB ψ (Bf B)) (muF B lf)) {φ : (ι → A F) → ℂ} (hφ : SB φ)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im) :
    cG B ρ P τ * theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) φ)
      (fun w => -(τ w)⁻¹) = theta B ρ P 1 (fun _ => 1) φ τ := by
  have hτ' : ∀ w, 0 < (-(τ w)⁻¹).im := by
    intro w
    have h0 : τ w ≠ 0 := fun h => by simpa [h] using hτ w
    simp only [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos (hτ w) (Complex.normSq_pos.mpr h0)
  have hsum : ∀ {σ : InfinitePlace F → ℂ}, (∀ w, 0 < (σ w).im) → ∀ {f : (ι → A F) → ℂ}, SB f →
      Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) f σ x‖ := fun hσ _ hf =>
    (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ 1 (fun _ => 1) (orth_one B ρ) _ hσ).1 _ hf
  have hsb : ∀ {f : (ι → A F) → ℂ}, SB f → SB (fou (chiB ψ (Bf B)) (muF B lf) f) := fun hf =>
    (GlobalTheory.T.fourier_inversion_schwartz_bruhat _ _ _ hV _ hf).1
  obtain ⟨N, hN, s, c, rfl⟩ := GlobalTheory.T.schwartz_bruhat_span_indicators F ι _ _ hV (fun N hN => (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.1) φ hφ
  have hI : ∀ a : ι → F, SB (indC N a) := (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.2
  classical
  have main : ∀ t : Finset (ι → F), SB (∑ a ∈ t, c a • indC N a) ∧
      cG B ρ P τ * theta B ρ P 1 (fun _ => 1)
        (fou (chiB ψ (Bf B)) (muF B lf) (∑ a ∈ t, c a • indC N a)) (fun w => -(τ w)⁻¹) =
      theta B ρ P 1 (fun _ => 1) (∑ a ∈ t, c a • indC N a) τ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have h0 : SB (0 : (ι → A F) → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      have hf0 : fou (chiB ψ (Bf B)) (muF B lf) (0 : (ι → A F) → ℂ) = 0 := by
        funext y
        simp [fou]
      have ht0 : ∀ σ, theta B ρ P 1 (fun _ => 1) (0 : (ι → A F) → ℂ) σ = 0 := by
        intro σ
        simp [theta, thTerm]
      simp only [Finset.sum_empty]
      exact ⟨h0, by rw [hf0, ht0, ht0, mul_zero]⟩
    | insert a t ha ih =>
      obtain ⟨ihs, ihe⟩ := ih
      have hca := sb_smul (c a) (hI a)
      simp only [Finset.sum_insert ha]
      refine ⟨sb_add hca ihs, ?_⟩
      rw [fou_add hV hca ihs, theta_add (hsum hτ' (hsb hca)) (hsum hτ' (hsb ihs)),
        theta_add (hsum hτ hca) (hsum hτ ihs), mul_add, ihe, fou_smul, theta_smul, theta_smul]
      congr 1
      rw [← base hl h1 hψ hQ hV a hN hτ]
      ring
  exact (main s).2

theorem thetaInvariance : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → cG B ρ P τ * theta B ρ P gf gi (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = theta B ρ P gf gi φ τ := by
  intro F _ _ _ _ lf hl h1 ψ hψ ι _ _ M B ρ P hQ gf gi hO φ hφ τ hτ
  obtain ⟨-, -, hsym, hdet, -, -, -⟩ := id hQ
  have hNA := GlobalTheory.T.weil_representation_quadratic_datum F lf hl h1 ψ hψ ι B hsym hdet
  have hV := hNA.2.2.2.2.2
  have hBu : IsUnit (Bf B).det := by
    have : (Bf B).det = algebraMap F (A F) B.det := by
      rw [Bf, RingHom.map_det]
      rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hdet).map _
  have hgu : IsUnit gf.det := by
    have h := congrArg det hO.1
    rw [det_mul, det_mul, det_transpose] at h
    have h2 : gf.det * gf.det = 1 := by
      apply hBu.mul_right_cancel
      linear_combination h
    exact IsUnit.of_mul_eq_one _ h2
  obtain ⟨-, hfou⟩ := GlobalTheory.T.weil_orthogonal_group_invariance (A F) ι ψ (hf F) (Bf B) (muF B lf) hNA gf hgu hO.1
  obtain ⟨hsb, hfy⟩ := hfou φ hφ
  have hQ' := GlobalTheory.T.quadratic_setup_invariant_under_isometry F ι M B ρ P gi hQ hO.2
  obtain ⟨hga, hgc⟩ := GlobalTheory.T.gaussian_change_of_variables_isometry F ι B ρ P gi hdet hO.2
  have hth : ∀ (f : (ι → A F) → ℂ) (σ : InfinitePlace F → ℂ), theta B ρ P gf gi f σ =
      theta B ρ (fun w => (gi w)ᵀ * P w * gi w) 1 (fun _ => 1) (fun x => f (gf *ᵥ x)) σ := by
    intro f σ
    refine tsum_congr fun x => ?_
    rw [thTerm_one]
    simp only [thTerm]
    rw [hga]
    rfl
  have hc := core hl h1 hψ hQ' hV hsb hτ
  rw [hth, hth, ← hc, hgc]
  congr 2
  funext y
  exact (hfy _).symm

end Base

end GlobalTheory.CompanionTheory.SW.ThW
