import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.DampedFunctionalEquationAtPoint

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

def WhittakerFunctionalEquationAdditive : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
  Integrable (onU (fun a => W (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 3 / 2))) (selfDualMeasure ψ) ∧
  Integrable (onU (fun a => W (dg2 a 1 * w0) * (((ω a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (-1 / 2 - s))) (selfDualMeasure ψ) ∧
  zA' ψ W ω μ s = G μ s * zA ψ W μ s

def GodementJacquetPrimalCoordinates : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ → ∀ s : ℂ, 0 < s.re →
  Integrable (gjI Φ W μ s) (LFS.hG ψ) ∧
  Integrable (fun p : (Fin 2 → F) × F => phk ψ Φ p.2 p.1 * zA ψ (fun g => W (g * (uni2 p.2 * hr p.1))) μ s)
    ((LFS.vol2 ψ).prod (selfDualMeasure ψ)) ∧
  GJ ψ Φ W μ s = itI ψ Φ (fun W' => zA ψ W' μ s) W

def GodementJacquetDualCoordinates : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ → ∀ s : ℂ, s.re < 1 →
  Integrable (gjdI ψ Φ W ω μ s) (LFS.hG ψ) ∧
  Integrable (fun p : (Fin 2 → F) × F => phk ψ Φ p.2 p.1 * zA' ψ (fun g => W (g * (uni2 p.2 * hr p.1))) ω μ s)
    ((LFS.vol2 ψ).prod (selfDualMeasure ψ)) ∧
  GJd ψ Φ W ω μ s = itI ψ Φ (fun W' => zA' ψ W' ω μ s) W

def GJFE : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ →
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (gjI Φ W μ s) (LFS.hG ψ) ∧ Integrable (gjdI ψ Φ W ω μ s) (LFS.hG ψ) ∧
      GJd ψ Φ W ω μ s = G μ s * GJ ψ Φ W μ s

open Classical in

def GJm1 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
  ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ r₂, ∫⁻ x, ∫⁻ y, (if h : y = 0 ∨ r₂ 1 = 0 then 0 else
    f (uni2 x * dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r₂) * ENNReal.ofReal ((modulus y : ℝ) ^ (-2 : ℤ)))
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ

open Classical in

def GJm2 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
  ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ r₂, ∫⁻ t, ∫⁻ y, (if h : y = 0 ∨ r₂ 1 = 0 then 0 else
    f (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * w0 * uni2 t * hr r₂) * ENNReal.ofReal ((modulus y : ℝ) ^ (-1 : ℤ)))
      ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ

def GodementKernelBigCell : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (y : Fˣ) (t : F) (r₂ : Fin 2 → F), r₂ 1 ≠ 0 →
  phd ψ Φ (dg2 y 1 * w0 * uni2 t * hr r₂) = phk ψ Φ t r₂

def GodementJacquetLeftTranslate : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ → ∀ h : GL (Fin 2) F,
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun g => Φ g.val * W (h * g) * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2))
      (LFS.hG ψ) ∧
    G μ s * ∫ g, Φ g.val * W (h * g) * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2)
      ∂LFS.hG ψ = (((μ (GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (-s - 1 / 2) *
        GJd ψ (fun X => Φ ((h⁻¹ : GL (Fin 2) F).val * X)) W ω μ s

def GodementSectionPartialFourier : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F →
  ∀ h : GL (Fin 2) F, LFS.Wp ψ W₀ Φ (em h) = mp (GeneralLinearGroup.det h) (1 / 2) *
    ∫ g, pFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (h * g⁻¹) ∂LFS.hG ψ

def SchwartzBruhatProductDecomposition : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F, ∃ (n : ℕ) (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
  (Φ₂ : Fin n → (Fin 2 → F) → ℂ), (∀ i, SB2 (Φ₁ i)) ∧ (∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F) ∧
    ∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y

def JacquetLanglandsDualIntegral : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (W' : GL (Fin 2) F → ℂ) (ω : Fˣ →* ℂˣ),
  (∀ (a : Fˣ) g, W' (dg2 a a * g) = ((ω a : ℂˣ) : ℂ) * W' g) → ∀ (ν : Fˣ →* ℂˣ) (x : GL (Fin 2) F) (s : ℂ),
    zJ (tr2 (dW2 W') x) ν (1 - s) = zJ' (tr2 W' (dl * tinv x)) ω ν⁻¹ s

def A1 : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ W' ∈ V',
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (iw (LFS.Wp ψ W₀ Φ) W' s) (mIw ψ) ∧
    Integrable (fun g => mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s) (LFS.hG ψ) ∧
    zetaGL3GL2 ψ (LFS.Wp ψ W₀ Φ) W' s = ∫ g, mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) (pFT ψ Φ g.val) s ∂LFS.hG ψ

def A2 : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ W' ∈ V',
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (iw (dW3 (LFS.Wp ψ W₀ Φ)) (dW2 W') (1 - s)) (mIw ψ) ∧
    Integrable (fun g => mp (GeneralLinearGroup.det g) (3 / 2 - s) * Z2 ψ (dW2 W₀) (tr2 (dW2 W') g) (dFT ψ Φ g.val) (1 - s)) (LFS.hG ψ) ∧
    zetaGL3GL2 ψ (dW3 (LFS.Wp ψ W₀ Φ)) (dW2 W') (1 - s) =
      ∫ g, mp (GeneralLinearGroup.det g) (3 / 2 - s) * Z2 ψ (dW2 W₀) (tr2 (dW2 W') g) (dFT ψ Φ g.val) (1 - s) ∂LFS.hG ψ

def A3 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (n : ℕ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (Φ₁ : Fin n → Matrix (Fin 2) (Fin 2) F → ℂ)
  (Φ₂ : Fin n → (Fin 2 → F) → ℂ), (∀ i, SB2 (Φ₁ i)) → (∀ i, Φ₂ i ∈ GodementSectionLocal.schwartzBruhat2 F) →
  (∀ A y, Φ (cat3 A y) = ∑ i, Φ₁ i A * Φ₂ i y) →
    (∀ A ξ, pFT ψ Φ A ξ = ∑ i, Φ₁ i A * ftN ψ (Φ₂ i) ξ) ∧ (∀ A ξ, dFT ψ Φ A ξ = ∑ i, matrixFourierTransposeInv ψ (Φ₁ i) A * Φ₂ i (-ξ))

def A4 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (W' : GL (Fin 2) F → ℂ) (g : GL (Fin 2) F), tr2 (dW2 W') g = dW2 (tr2 W' (tinv g))

def A5 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ V : GL (Fin 2) F → ℂ) (α β : Fˣ →* ℂˣ),
  (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = ((α a : ℂˣ) : ℂ) * W₀ g) → (∀ (a : Fˣ) g, V (dg2 a a * g) = ((β a : ℂˣ) : ℂ) * V g) →
  ∀ (φ : (Fin 2 → F) → ℂ) (s : ℂ), Z2 ψ W₀ V (fun ξ => φ (-ξ)) s = ((α (-1) * β (-1) : ℂˣ) : ℂ) * Z2 ψ W₀ V φ s

def A6 : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (z2I W₀ V φ s) (mIw ψ) ∧ Integrable (z2I (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s)) (mIw ψ) ∧
    Z2 ψ (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s) = ((ω (-1) : ℂˣ) : ℂ) * G ν s * G ν⁻¹ s * Z2 ψ W₀ V φ s

def DampedDataFunctionalEquation : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (δ : ℝ) (ν' : Fˣ →* ℂˣ),
  (∀ a, ((ν' a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a δ) → ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, δ < 0 → 0 < s.re + δ → s.re - δ < 1 →
    Integrable (z2I (W2 ψ ν' ν'⁻¹ φ₀) V φ s) (mIw ψ) ∧
    Integrable (z2I (dW2 (W2 ψ ν' ν'⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s)) (mIw ψ) ∧
    Z2 ψ (dW2 (W2 ψ ν' ν'⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s) =
      ((ω (-1) : ℂˣ) : ℂ) * G ν (s + δ) * G ν⁻¹ (s - δ) * Z2 ψ (W2 ψ ν' ν'⁻¹ φ₀) V φ s

def A6lim : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (ν' : ℕ → Fˣ →* ℂˣ) (δ : ℕ → ℝ),
  (∀ n a, ((ν' n a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a (δ n)) → Filter.Tendsto δ Filter.atTop (nhds 0) →
  ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V', ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Filter.Tendsto (fun n => Z2 ψ (W2 ψ (ν' n) (ν' n)⁻¹ φ₀) V φ s) Filter.atTop (nhds (Z2 ψ (W2 ψ ν ν⁻¹ φ₀) V φ s)) ∧
    Filter.Tendsto (fun n => Z2 ψ (dW2 (W2 ψ (ν' n) (ν' n)⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s)) Filter.atTop
      (nhds (Z2 ψ (dW2 (W2 ψ ν ν⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s)))

def Gcont : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => (∃ V ∈ V', V ≠ 0) → ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ →
  ContinuousOn (G μ) {s : ℂ | 0 < s.re ∧ s.re < 1}

def A6gj : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∃ C : ℂ, C ≠ 0 ∧ ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (δ : ℝ) (ν' : Fˣ →* ℂˣ),
  (∀ a, ((ν' a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a δ) → ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, δ < 0 → 0 < s.re + δ → s.re < 1 →
    Integrable (fun p : GL (Fin 2) F × Fˣ => φ₀ (e1r p.1) * φ (e2r p.1) * (((ν' (GeneralLinearGroup.det p.1))⁻¹ : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det p.1) (s + 1 / 2) * (V (dg2 p.2 1 * p.1) * ((ν' p.2 : ℂˣ) : ℂ) * mp p.2 (s - 1 / 2)))
      ((LFS.hG ψ).prod (multHaar F)) ∧
    Z2 ψ (W2 ψ ν' ν'⁻¹ φ₀) V φ s = C * ∫ g, φ₀ (e1r g) * φ (e2r g) * (((ν' (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
      mp (GeneralLinearGroup.det g) (s + 1 / 2) * zJ (tr2 V g) ν' s ∂LFS.hG ψ

def GJcl : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ → ∀ h : GL (Fin 2) F,
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun g => Φ g.val * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2) * W (h * g))
      (LFS.hG ψ) ∧
    Integrable (fun g => matrixFourierTransposeInv ψ Φ (tinv g).val * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s - 3 / 2) *
      W (h * g)) (LFS.hG ψ) ∧
    ∫ g, matrixFourierTransposeInv ψ Φ (tinv g).val * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s - 3 / 2) * W (h * g) ∂LFS.hG ψ =
      ((ω (-1) : ℂˣ) : ℂ) * G μ s *
        ∫ g, Φ g.val * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2) * W (h * g) ∂LFS.hG ψ

def A7 : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ W' ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ Φ₁, SB2 Φ₁ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun g => Φ₁ g.val * mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) φ s) (LFS.hG ψ) ∧
    Integrable (fun g => matrixFourierTransposeInv ψ Φ₁ (tinv g).val * mp (GeneralLinearGroup.det g) (s - 3 / 2) * Z2 ψ W₀ (tr2 W' g) φ s) (LFS.hG ψ) ∧
    ∫ g, matrixFourierTransposeInv ψ Φ₁ (tinv g).val * mp (GeneralLinearGroup.det g) (s - 3 / 2) * Z2 ψ W₀ (tr2 W' g) φ s ∂LFS.hG ψ =
      ((ω (-1) : ℂˣ) : ℂ) * G 1 s * ∫ g, Φ₁ g.val * mp (GeneralLinearGroup.det g) (s + 1 / 2) * Z2 ψ W₀ (tr2 W' g) φ s ∂LFS.hG ψ

def A8 : Prop := ForS fun F _ _ _ _ _ _ ψ => MeasurePreserving (tinv : GL (Fin 2) F → GL (Fin 2) F) (LFS.hG ψ) (LFS.hG ψ)

def A9 : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F,
  ftN ψ φ ∈ GodementSectionLocal.schwartzBruhat2 F ∧ ftP ψ (ftN ψ φ) = φ

def GodementSectionDual : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F,
  dW3 (LFS.Wp ψ W₀ Φ) (em h) = mp (GeneralLinearGroup.det h) (1 / 2) *
    ∫ g, dFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * dW2 W₀ (h * g⁻¹) ∂LFS.hG ψ

def GodementSectionDualInverse : Prop := ForS fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ : Fˣ →* ℂˣ, Continuous μ₁ → Continuous μ₂ →
  ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F,
    dW2 (W2 ψ μ₁ μ₂ φ₀) = fun g => ((μ₂ (-1) : ℂˣ) : ℂ) * W2 ψ⁻¹ μ₁⁻¹ μ₂⁻¹ (ftN ψ φ₀) g

def DampedGodementJacquetForm : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∃ C : ℂ, C ≠ 0 ∧ ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (δ : ℝ) (ν' : Fˣ →* ℂˣ),
  (∀ a, ((ν' a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a δ) → ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ,
    (δ < 0 → 0 < s.re + δ → s.re < 1 →
      Integrable (gjPI φ₀ φ V ν' s) ((LFS.hG ψ).prod (multHaar F)) ∧ Z2 ψ (W2 ψ ν' ν'⁻¹ φ₀) V φ s = C * gjP ψ φ₀ φ V ν' s) ∧
    (0 < δ → δ < 1 / 2 → 0 < s.re → s.re < 1 / 2 →
      Integrable (z2I (dW2 (W2 ψ ν' ν'⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s)) (mIw ψ) ∧
      Z2 ψ (dW2 (W2 ψ ν' ν'⁻¹ φ₀)) (dW2 V) (ftP ψ φ) (1 - s) = C * G ν (s + δ) * gjE ψ φ₀ φ V ν' s)

def A6gcl : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (δ : ℝ) (ν' : Fˣ →* ℂˣ),
  (∀ a, ((ν' a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a δ) → ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, δ < 0 → 0 < s.re + δ → s.re < 1 / 2 →
    Integrable (gjPI φ₀ φ V ν' s) ((LFS.hG ψ).prod (multHaar F)) ∧
    Integrable (gjEI ψ φ₀ φ V ν' s) ((LFS.hG ψ).prod (multHaar F)) ∧
    gjE ψ φ₀ φ V ν' s = ((ω (-1) : ℂˣ) : ℂ) * G ν⁻¹ (s - δ) * gjP ψ φ₀ φ V ν' s

def Econt : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ (ν' : ℕ → Fˣ →* ℂˣ) (δ : ℕ → ℝ),
  (∀ n a, ((ν' n a : ℂˣ) : ℂ) = ((ν a : ℂˣ) : ℂ) * mp a (δ n)) → Filter.Tendsto δ Filter.atTop (nhds 0) →
  ∀ φ₀ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ V ∈ V', ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ,
    0 < s.re → s.re < 1 / 2 →
      Filter.Tendsto (fun n => gjE ψ φ₀ φ V (ν' n) s) Filter.atTop (nhds (gjE ψ φ₀ φ V ν s))

def A6int : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (z2I W₀ V φ s) (mIw ψ) ∧ Integrable (z2I (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s)) (mIw ψ)

def Z2cs : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ V ∈ V',
  ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F,
    ContinuousOn (fun s => Z2 ψ W₀ V φ s) {s : ℂ | 0 < s.re ∧ s.re < 1} ∧
    ContinuousOn (fun s => Z2 ψ (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s)) {s : ℂ | 0 < s.re ∧ s.re < 1}

def WhTdual : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => WhT ψ ω⁻¹ (fun μ s => (G μ⁻¹ (1 - s))⁻¹) (V'.map dualWhittakerLocal)

def A6on (P : ℂ → Prop) : Prop := ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹,
  ∀ V ∈ V', ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ s : ℂ, P s → DampedFunctionalEquationAtPoint ψ ω G ν W₀ V φ s

def A6lo : Prop := A6on fun s => 0 < s.re ∧ s.re < 1 / 2
def A6hi : Prop := A6on fun s => 1 / 2 < s.re ∧ s.re < 1
def A6ctr : Prop := A6on fun s => s.re = 1 / 2

def SGen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν →
    ∀ ω G V', IsUnit1 ω → WhT ψ⁻¹ ω G V' → ∀ W₀ ∈ V2 ψ ν ν⁻¹, ∀ Φ ∈ LFS.SB F, ∀ W' ∈ V', ∀ s : ℂ, 0 < s.re → s.re < 1 →
      FunctionalEquationPair ψ ν ω G (LFS.Wp ψ W₀ Φ) W' s

end Ad3.K.GL2LocalData
