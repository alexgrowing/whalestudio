import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace Ad3.R

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], AddChar F Circle → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), IsStd ψ → P F ψ

def ForK (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin 2) F)], AddChar F Circle → Measure (integralGL F 2) → Prop) : Prop :=
  ForF fun F _ _ _ _ _ _ ψ => ∀ [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] (m : Measure (integralGL F 2))
    [m.IsHaarMeasure] [IsProbabilityMeasure m], P F ψ m

def Strip (s : ℂ) : Prop := 0 < s.re ∧ s.re < 1

def A1 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (h : GL (Fin 2) F), SB φ →
  SB (fun r => φ (r ᵥ* (h : Matrix (Fin 2) (Fin 2) F))) ∧ SB (sF ψ φ) ∧ (∀ z : ℂ, W2 ψ μ₁ μ₂ (z • φ) = z • W2 ψ μ₁ μ₂ φ) ∧
  ∀ g, W2 ψ μ₁ μ₂ φ (g * h) = ((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2) *
    W2 ψ μ₁ μ₂ (fun r => φ (r ᵥ* (h : Matrix (Fin 2) (Fin 2) F))) g

def A2 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∃ C : ℂ, C ≠ 0 ∧
  (∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C * ∫ t, G t ∂selfDualMeasure ψ) ∧
  ∀ f₁ ∈ schwartzBruhat F, ∀ f₃ ∈ schwartzBruhat F, ∀ (u₁ u₃ : Fˣ) (c : Fˣ →* ℂˣ), IsUnit1 c → ∀ s, Strip s →
    ∫ a : Fˣ, (∫ y, f₁ y * (ψ (-(y * a * (u₁⁻¹ : Fˣ))) : ℂ) ∂selfDualMeasure ψ) *
        (∫ y, f₃ y * (ψ (y * a * (u₃⁻¹ : Fˣ)) : ℂ) ∂selfDualMeasure ψ) * ((c a : ℂˣ) : ℂ) * mp a s ∂multHaar F =
      C * gam ψ c⁻¹ (1 - s) * ∫ p : F × F, f₁ p.1 * f₃ p.2 * chF c⁻¹ (-s) (p.2 * (u₃⁻¹ : Fˣ) - p.1 * (u₁⁻¹ : Fˣ))
        ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ))

def A4 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (ν c : Fˣ →* ℂˣ), IsUnit1 ν → IsUnit1 c → ∀ s, Strip s →
  Measurable (fun p : (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.2.1 p.1 p.2.2) ∧
  ∀ B : Set (Fin 2 → F), IsCompact B → IntegrableOn (fun p : (Fin 2 → F) × (Fin 2 → F) => Kr ν c s p.1 ![0, 1] p.2)
    (B ×ˢ B) ((m2 ψ).prod (m2 ψ))

def A3 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∃ C : ℂ, C ≠ 0 ∧ ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
    ∀ φ₁ φ₃, SB φ₁ → SB φ₃ → ∀ s, Strip s → Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s 1 = C * gam ψ c⁻¹ (1 - s) *
      ∫ p : (Fin 2 → F) × (Fin 2 → F), φ₁ p.1 * conj (φ₃ p.2) * Kr (μ₂ * μ₁⁻¹) c s p.1 ![0, 1] p.2 ∂((m2 ψ).prod (m2 ψ))

def A5 : Prop := ForK fun F _ _ _ _ _ _ _ ψ m => ∃ C : NNReal, C ≠ 0 ∧
  m2 ψ = C • Measure.map (fun p : integralGL F 2 × Fˣ => ![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F))
    (m.prod ((multHaar F).withDensity fun z => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)))

def A6 : Prop := ForK fun F _ _ _ _ _ _ _ ψ m => ∃ C : ℂ, C ≠ 0 ∧ ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
  ∀ φ₁ φ₃ Ψ, SB φ₁ → SB φ₃ → SB Ψ → ∀ s, Strip s →
    Integrable (triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃) ((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) ∧
    Zv m (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) Ψ c s =
      C * gam ψ c⁻¹ (1 - s) * ∫ p, triI (μ₂ * μ₁⁻¹) c s φ₁ Ψ φ₃ p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ)))

def A7 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (χ₁ χ₂ : Fˣ →* ℂˣ), IsUnit1 χ₁ → IsUnit1 χ₂ → ∀ f, SB f → ∀ s, Strip s →
  ∫ r, (∫ r', f r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) * (chF χ₁⁻¹ (-s) (r 0) * chF χ₂⁻¹ (-s) (r 1)) ∂m2 ψ =
    gam ψ χ₁ s * gam ψ χ₂ s * ∫ r, f r * (chF χ₁ (s - 1) (r 0) * chF χ₂ (s - 1) (r 1)) ∂m2 ψ

def A8 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (ν c : Fˣ →* ℂˣ), IsUnit1 ν → IsUnit1 c → ∀ Ψ, SB Ψ → ∀ s, Strip s →
  ∀ r₁ r₃ : Fin 2 → F, ∫ r, sF ψ Ψ r * Kr ν c⁻¹ (1 - s) r₁ r r₃ ∂m2 ψ =
    gam ψ (ν * c) s * gam ψ (ν⁻¹ * c) s * (((ν * c) (-1) : ℂˣ) : ℂ) * ∫ r, Ψ r * Kr ν c s r₁ r r₃ ∂m2 ψ

def LocalGammaFunctionalEquation : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ c : Fˣ →* ℂˣ, IsUnit1 c →
  DifferentiableOn ℂ (gam ψ c) {s | Strip s} ∧ ∀ s, Strip s → gam ψ c s * gam ψ c⁻¹ (1 - s) = ((c (-1) : ℂˣ) : ℂ)

def A9 : Prop := ForK fun F _ _ _ _ _ _ _ ψ m => ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
  ∀ φ₁ Ψ, SB φ₁ → SB Ψ → ∀ (x : F) s, Strip s →
    Zv m (W2 ψ μ₁ μ₂ φ₁) (fun g => W2 ψ μ₁ μ₂ φ₁ (g * uni2 x)) (sF ψ Ψ) c⁻¹ (1 - s) =
      (((μ₁ * μ₂) (-1) : ℂˣ) : ℂ) * gam ψ c s * gam3 ψ (μ₁ * μ₂⁻¹) c s *
        Zv m (W2 ψ μ₁ μ₂ φ₁) (fun g => W2 ψ μ₁ μ₂ φ₁ (g * uni2 x)) Ψ c s

def A10 : Prop := ForK fun F _ _ _ _ _ _ _ ψ m => ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
  ∀ W ∈ V2 ψ μ₁ μ₂, ∀ W' ∈ V2 ψ μ₁ μ₂, (∀ s : ℂ, 0 < s.re → (∀ κ ∈ integralGL F 2, Integrable
      (fun a => W (dg2 a 1 * κ) * conj (W' (dg2 a 1 * κ)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) (multHaar F)) ∧
      IsLocallyConstant (Av W W' c s)) ∧
    ∀ Ψ, SB Ψ → (∀ s : ℂ, 0 < s.re → IsLocallyConstant (GodementSectionLocal.localSection c c⁻¹ s Ψ)) ∧
      DifferentiableOn ℂ (Zv m W W' Ψ c) {s | 0 < s.re}

def A11 : Prop := ForK fun F _ _ _ _ _ _ _ ψ m => ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
  ∀ W ∈ V2 ψ μ₁ μ₂, W 1 ≠ 0 → ∀ s : ℂ, 0 < s.re → ∃ (x : F) (Ψ : (Fin 2 → F) → ℂ), SB Ψ ∧
    Zv m W (fun g => W (g * uni2 x)) Ψ c s ≠ 0

def U1 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (ω : Fˣ →* ℂˣ) (n : ℕ) (lam : ℂ) (W : GL (Fin 2) F → ℂ), 1 ≤ n → lam ≠ 0 →
  Law ψ ω W → TypeU ω n lam W → W 1 = 0 → W = 0

def U0 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (ω : Fˣ →* ℂˣ) (lam : ℂ) (W : GL (Fin 2) F → ℂ),
  Law ψ ω W → TypeT lam W → W 1 = 0 → W = 0

def M1 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnramifiedChar μ₂ →
  1 ≤ quasiCharConductor μ₁ → ∃ φ, SB φ ∧ W2 ψ μ₁ μ₂ φ 1 = 1 ∧ TypeU (μ₁ * μ₂) (quasiCharConductor μ₁)
    ((Real.sqrt (residueCard F) : ℝ) * ((μ₂ (unifUnit F) : ℂˣ) : ℂ)) (W2 ψ μ₁ μ₂ φ)

def M0 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnramifiedChar μ₁ →
  IsUnramifiedChar μ₂ → SB (ind0 : (Fin 2 → F) → ℂ) ∧ W2 ψ μ₁ μ₂ ind0 1 = 1 ∧
    TypeT ((Real.sqrt (residueCard F) : ℝ) * (((μ₁ (unifUnit F) : ℂˣ) : ℂ) + ((μ₂ (unifUnit F) : ℂˣ) : ℂ))) (W2 ψ μ₁ μ₂ ind0)

def E4 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c → IsUnramifiedChar μ₁ →
  IsUnramifiedChar μ₂ → IsUnramifiedChar c → ∀ s : ℂ, 0 < s.re → ∀ G : Fˣ → ℂ,
    (∀ a, G a = W2 ψ μ₁ μ₂ ind0 (dg2 a 1) * conj (W2 ψ μ₁ μ₂ ind0 (dg2 a 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) →
    (∀ a u : Fˣ, ord (u : F) = 0 → G (a * u) = G a) ∧ (∀ a : Fˣ, G a ≠ 0 → (a : F) ∈ 𝒪[F]) ∧ G 1 = 1 ∧
    (∀ n : ℕ, ‖G (unifUnit F ^ n)‖ ≤ ((n : ℝ) + 1) ^ 2 * (residueCard F : ℝ) ^ (-(n * s.re))) ∧
    (∑' n : ℕ, G (unifUnit F ^ n)) * localLFactor (c * c) (2 * s) = lf3 (μ₁ * μ₂⁻¹) c s * localLFactor c s

def U2 : Prop := ForF fun F _ _ _ _ _ _ _ => ∀ ω : Fˣ →* ℂˣ, Continuous ω → 1 ≤ quasiCharConductor ω → ∀ y : F, ord y = -1 →
  ∃ x d x' d', GammaZeroLevelMembership (quasiCharConductor ω) x d ∧ GammaZeroLevelMembership (quasiCharConductor ω) x' d' ∧ x * uni2 y = uni2 y * x' ∧ ω d ≠ ω d'

def C1 : Prop := ForF fun F _ _ _ _ _ _ _ => (∃ (ϖ : Fˣ) (B : Finset F), Reps ϖ B) ∧ (∀ (ϖ : Fˣ) B, Reps ϖ B → B.card = residueCard F) ∧
  ∀ (ω : Fˣ →* ℂˣ) (n : ℕ) (f : GL (Fin 2) F → ℂ), 1 ≤ n → unitFiltrationUnits F n ≤ ω.ker →
    (∀ x d, GammaZeroLevelMembership n x d → ∀ g, f (g * x) = ((ω d : ℂˣ) : ℂ) * f g) → ∀ ϖ B ϖ' B', Reps ϖ B → Reps ϖ' B' → ∀ x d, GammaZeroLevelMembership n x d → ∀ g : GL (Fin 2) F,
      ∑ b ∈ B, f (g * x * upm ϖ b) = ((ω d : ℂˣ) : ℂ) * ∑ b ∈ B', f (g * upm ϖ' b)

def C0 : Prop := ForF fun F _ _ _ _ _ _ _ => ∀ f : GL (Fin 2) F → ℂ, (∀ x ∈ integralGL F 2, ∀ g, f (g * x) = f g) →
  ∀ ϖ B ϖ' B', Reps ϖ B → Reps ϖ' B' → ∀ x ∈ integralGL F 2, ∀ g : GL (Fin 2) F,
    ∑ b ∈ B, f (g * x * upm ϖ b) + f (g * x * dg2 1 ϖ) = ∑ b ∈ B', f (g * upm ϖ' b) + f (g * dg2 1 ϖ')

def B0 : Prop := (∀ v : Pl, IsStd (localAdelicChar ℚ v) ∧ residueCard (Qv v) = pOf v ∧ (pOf v).Prime ∧
    ord ((pOf v : ℕ) : Qv v) = 1 ∧ (∀ n : ℕ, n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v)) ∧
    (∀ x, ∃ h, IsLoc2 v x h) ∧ ∀ c : HeckeCharacter ℚ, IsUnit1 (localChar c v)) ∧
  Function.Injective pOf ∧ (∀ p : ℕ, p.Prime → ∃ v, pOf v = p) ∧
  (∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g') ∧
  (∀ (S : Finset Pl) (x : ∀ v : S, Qv v.1), ∃ h, IsUn S x h) ∧ (∃ m, IsK m) ∧
  (∀ g : G2, {v | finAt v g ∉ integralGL (Qv v) 2}.Finite) ∧
  ∀ (v : Pl) (x : Qv v) (a d : (Qv v)ˣ), ∃ (x' : 𝔸[ℚ]) (a' d' : Jd), IsLoc2 v (uni2 x) (uni2 x') ∧ IsLoc2 v (dg2 a d) (dg2 a' d') ∧
    adelicChar ℚ x' = localAdelicChar ℚ v x ∧ (a = d → a' = d') ∧
    ∀ c : HeckeCharacter ℚ, (c.toIdele a' : ℂ) = localChar c v a ∧ (c.toIdele d' : ℂ) = localChar c v d

def D0 : Prop := ∃ 𝓓 : Set Jd, MeasurableSet 𝓓 ∧ (∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓) ∧
  ∀ (τ : ℝ) (M : ℕ), 0 < τ → τ < M → ∫⁻ a in 𝓓, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞

def G0 : Prop := ∃ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓

def G1a : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → μ {g | Dt g = 1} = 0 ∧
  (∀ r : ℝ, 0 < r → ∃ z : Jd, md z ^ 2 = r ∧ ∀ c : HeckeCharacter ℚ, IsOfFinOrder c → c.toIdele z = 1) ∧
  ∀ T : G2 → G2, (T = inv2 ∨ (∃ h, T = fun g => g * h) ∨ ∃ z : Jd, T = fun g => dg2 z z * g) →
    (∀ F : G2 → ℝ≥0∞, Measurable F → LInv F → ∫⁻ g in 𝓕, F (T g) ∂μ = ∫⁻ g in 𝓕, F g ∂μ) ∧
    ∀ F : G2 → ℂ, Measurable F → LInv F → ∫ g in 𝓕, F (T g) ∂μ = ∫ g in 𝓕, F g ∂μ

def G1 : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ F : G2 → ℂ, Continuous F → (∃ C, ∀ g, ‖F g‖ ≤ C) → LInv F →
  (CInv F → ∀ h, ∫ g in 𝓕 ∩ band, F (g * h) ∂μ = ∫ g in 𝓕 ∩ band, F g ∂μ) ∧
  (∀ (η : HeckeCharacter ℚ), IsOfFinOrder η → (∀ (z : Jd) g, F (dg2 z z * g) = (η.toIdele z : ℂ) * F g) → η ≠ 1 →
    ∫ g in 𝓕 ∩ band, F g ∂μ = 0) ∧
  (CInv F → F ≠ 0 → ∫ g in 𝓕 ∩ band, F g * conj (F g) ∂μ ≠ 0)

def G2a : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∃ C, Coord μ mK C

def G2b : Prop := ∀ μ 𝓕 mK 𝓓 C, Set0 μ 𝓕 mK 𝓓 → Coord μ mK C → ∀ (H : G2 → ℝ≥0∞) (Φ : (Fin 2 → 𝔸[ℚ]) → ℝ≥0∞),
  Measurable H → LInv H → Measurable Φ →
  ∫⁻ g in 𝓕, H g * ∑' ξ : NZ, Φ (row ξ.1 g) ∂μ = C * ∫⁻ κ, ∫⁻ z, ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
    H (pt x a z κ.1) * Φ (lrow z κ.1) * ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK

def G2c : Prop := ∀ μ 𝓕 mK 𝓓 C, Set0 μ 𝓕 mK 𝓓 → Coord μ mK C → ∀ (H : G2 → ℂ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ),
  Measurable H → LInv H → Measurable Φ → ∫⁻ g in 𝓕, ‖H g‖ₑ * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞ →
  ∫ g in 𝓕, H g * th Φ g ∂μ = (C : ℝ) * ∫ κ, ∫ z, ∫ a in 𝓓, ∫ x in fundamentalSet ℚ,
    H (pt x a z κ.1) * Φ (lrow z κ.1) * (((md a)⁻¹ : ℝ) : ℂ) ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK

def G3a : Prop := ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, Continuous Φ ∧ ∀ τ : ℝ, 1 < τ → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ κ : KA,
  ∫⁻ z, ‖Φ (lrow z κ.1)‖ₑ * ENNReal.ofReal (md z ^ τ) ∂ideleMeasure ℚ ≤ C

def G3 : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ H, Aut H → ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, ∀ σ : ℝ, 1 < σ →
  Measurable (th Φ) ∧ LInv (th Φ) ∧
  ∫⁻ g in 𝓕, (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞

def AdelicThetaPoissonSummation : Prop := ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, sFA Φ ∈ Adele2.schwartzBruhat2 ℚ ∧ sFA (sFA Φ) 0 = Φ 0 ∧
  ∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th (sFA Φ) (inv2 g) + sFA Φ 0)

def G4 : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ H, Aut H → ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, ∀ c : HeckeCharacter ℚ, IsOfFinOrder c →
  ∃ E E' : ℂ → ℂ, DifferentiableOn ℂ E {s | 0 < s.re} ∧ DifferentiableOn ℂ E' {s | 0 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → E s = (1 - 2 ^ (1 - s)) * Zg μ 𝓕 H c Φ s ∧ E' s = (1 - 2 ^ (1 - s)) * Zg μ 𝓕 H c⁻¹ (sFA Φ) s) ∧
    (∀ s, Strip s → (1 - 2 ^ s) * E s = (1 - 2 ^ (1 - s)) * E' (1 - s)) ∧
    (E 1 ≠ 0 → ∫ g in 𝓕 ∩ band, H g * cdet c g ∂μ ≠ 0)

def G5 : Prop := ∀ μ 𝓕 mK 𝓓 C, Set0 μ 𝓕 mK 𝓓 → Coord μ mK C → ∀ H P, Aut H → Par H P →
  ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, ∀ (c : HeckeCharacter ℚ) (s : ℂ), 1 < s.re → Zg μ 𝓕 H c Φ s = (C : ℝ) * Jg mK P c Φ s

def E1 : Prop := ∀ (S : Finset Pl) (A : ∀ v : S, (Qv v.1)ˣ → ℂ) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (σ : ℝ), 1 < σ →
  (∀ v, Integrable (A v) (multHaar (Qv v.1))) →
  (∀ v ∉ S, (∀ a u : (Qv v)ˣ, ord (u : Qv v) = 0 → G v (a * u) = G v a) ∧ (∀ a, G v a ≠ 0 → (a : Qv v) ∈ 𝒪[Qv v]) ∧ G v 1 = 1 ∧
    ∀ n : ℕ, ‖G v (unifUnit (Qv v) ^ n)‖ ≤ ((n : ℝ) + 1) ^ 2 * (pOf v : ℝ) ^ (-(n * σ))) →
  Multipliable (fun v : {v : Pl // v ∉ S} => ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)) ∧
  ∫ a : Afˣ, (∏ v : S, A v (lf v.1 a)) * ∏ᶠ v : {v : Pl // v ∉ S}, G v.1 (lf v.1 a) ∂finiteIdeleMeasure ℚ =
    (∏ v : S, ∫ a, A v a ∂multHaar (Qv v.1)) * ∏' v : {v : Pl // v ∉ S}, ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)

def E2 : Prop := ∀ (S : Finset Pl) (s : ℂ), 1 < s.re →
  (∀ c : HeckeCharacter ℚ, (∀ v ∉ S, IsUnramifiedChar (localChar c v)) → (∀ v : Pl, v.asIdeal ∣ c.conductor → v ∈ S) ∧
    HasProd (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s) (partialLFunction c S s)) ∧
  ∀ ν : ∀ v : Pl, (Qv v)ˣ →* ℂˣ, (∀ v, IsUnit1 (ν v)) → Multipliable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s

def E3 : Prop := ∀ (mK : Measure KA) [mK.IsHaarMeasure] [IsProbabilityMeasure mK] m, IsK m → ∀ (S : Finset Pl)
  (A : ∀ v : S, GL (Fin 2) (Qv v.1) → ℂ), (∀ v, IsLocallyConstant (A v)) →
  ∫ κ : KA, ∏ v : S, A v (finAt v.1 κ.1) ∂mK = ∏ v : S, ∫ κ, A v κ.1 ∂m v.1

def GS : Prop := ∃ γ, IsGauss γ

def FT : Prop := ∀ γ, IsGauss γ → ∀ (S : Finset Pl) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) →
  tst γ S Ψ ∈ Adele2.schwartzBruhat2 ℚ ∧ sFA (tst γ S Ψ) = tst γ S fun v => sF (localAdelicChar ℚ v.1) (Ψ v)

def E5 : Prop := ∀ k : ℕ, 1 ≤ k → ∃ C : ℂ, C ≠ 0 ∧ ∀ γ, IsGauss γ → ∀ (c : HeckeCharacter ℚ) (δ : Bool), IsOfFinOrder c →
  (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → ∀ s : ℂ, 1 < s.re → ∀ (κ : KA) (Q : GL (Fin 2) ℝ → ℂ),
    (∀ (t : ℝˣ) (r : GL (Fin 2) ℝ), r.val * r.valᵀ = 1 → r.det.val = 1 → Q (dg2 t 1 * r) = WR k t * conj (WR k t)) →
    archSection c c⁻¹ s γ (AdelicGLn.prodEquiv ℚ 2 κ.1).1 *
      ∫ a : (InfiniteAdeleRing ℚ)ˣ, Q (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ =
      C * (if δ then -1 else 1) * GG k s

def H1 : Prop := ∀ (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Pl), IsOfFinOrder c →
  (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) →
  ∃ L L' : ℂ → ℂ, Differentiable ℂ L ∧ Differentiable ℂ L' ∧
    (∀ s : ℂ, 1 < s.re → L s = (s - 1) * Lp c S s ∧ L' s = (s - 1) * Lp c⁻¹ S s ∧ L' s ≠ 0) ∧
    (∀ s, Strip s → -s * L s * Complex.Gammaℝ (s + if δ then 1 else 0) = (s - 1) * ((if δ then -Complex.I else 1) *
      Complex.Gammaℝ (1 - s + if δ then 1 else 0)) * (∏ v ∈ S, gam (localAdelicChar ℚ v) (localChar c v) s) * L' (1 - s)) ∧
    (c = 1 → L 1 ≠ 0) ∧ (c ≠ 1 → L 1 = 0 ∧ deriv L 1 ≠ 0)

def ForE (P : ∀ (k N : ℕ) [NeZero N], DirichletCharacter ℂ N → (ℕ → ℂ) → HeckeCharacter ℚ → (G2 → ℂ) → Prop) : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ f a, IsForm k N χ f a → IsEig k N χ a →
    ∀ ω φ, Om N χ ω → Lift k N f ω φ → P k N χ a ω φ

def F0 : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ∃ ω, Om N χ ω

def F0b : Prop := ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ (-1) = (-1) ^ k → ∀ ω, Om N χ ω → OmL k N χ ω

def F1 : Prop := ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a → a 1 = 1 → ∀ ω, Om N χ ω →
  χ (-1) = (-1) ^ k ∧ ∃ φ, Lift k N f ω φ

def AutomorphicLevelEquivariance : Prop := ForE fun _ N _ _ _ ω φ =>
  (∀ v, ¬ pOf v ∣ N → ∀ x ∈ integralGL (Qv v) 2, ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = φ g) ∧
  (∀ v, pOf v ∣ N → ∀ x d, GammaZeroLevelMembership (N.factorization (pOf v)) x d → ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = (localChar ω v d : ℂ) * φ g) ∧
  ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g

def HeckeSumLocalTranslates : Prop := ForE fun k N _ _ a _ φ => ∀ v (ϖ : (Qv v)ˣ), (ϖ : Qv v) = (pOf v : ℕ) → ∀ (t : ℕ → G2) (t' : G2),
  (∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b)) → IsLoc2 v (dg2 1 ϖ) t' → ∀ x : GL (Fin 2) ℝ, 0 < x.det.val →
    ∑ b ∈ Finset.range (pOf v), φ (realEmb x * t b) + (if pOf v ∣ N then 0 else φ (realEmb x * t')) = lamOf k a v * φ (realEmb x)

def F3 : Prop := ForE fun k N _ _ a ω φ => Hk k N a ω φ

def F2 : Prop := ForE fun k _ _ _ _ ω φ => Continuous (Wh φ) ∧ (∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g) ∧
  (∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g) ∧ ∀ t : ℝˣ, Wh φ (realEmb (dg2 t 1)) = WR k t

def F5 : Prop := ForE fun _ _ _ _ _ _ φ => (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ h : G2, (∀ w, infAt w h = 1) → Dec fun g => φ (g * h)

def F4 : Prop := ForE fun k N _ _ a _ _ => ∀ v, pOf v ∣ N → ‖lamOf k a v‖ ^ 2 = pOf v

def F6 : Prop := ∀ φ φ' : G2 → ℂ, Continuous φ → Continuous φ' → LInv φ → LInv φ' → Dec φ → (∃ C : ℝ, ∀ g, ‖φ' g‖ ≤ C) →
  (∀ g, ∫ x in fundamentalSet ℚ, φ (uni2 x * g) ∂adeleMeasure ℚ = 0) → Continuous (Wh φ) → Continuous (Wh φ') →
  Par (fun g => φ g * conj (φ' g)) fun g => Wh φ g * conj (Wh φ' g)

def ConstantTermVanishingAlt : Prop := ForE fun _ _ _ _ _ _ φ => ∀ g, ∫ x in fundamentalSet ℚ, φ (uni2 x * g) ∂adeleMeasure ℚ = 0

def F7 : Prop := ForE fun k N _ χ a ω φ => Pure k N χ a → ∃ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ ∧
  ∀ v, ¬ pOf v ∣ N → ∃ α β : ℂˣ, (α : ℂ) + β = a (pOf v) ∧ (α : ℂ) * β = χ (pOf v) * (pOf v : ℂ) ^ (k - 1) ∧
    (μ₁ v * (μ₂ v)⁻¹) (unifUnit (Qv v)) = α / β

def E0 : Prop := ForE fun _ N _ _ _ ω φ => ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ g : G2,
  Wh φ g = Wh φ (realEmb (realPart g)) * ∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)

def UnramifiedEulerProductIntegral : Prop := ForE fun _ N _ _ _ ω φ => ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ (S : Finset Pl), (∀ v, pOf v ∣ N → v ∈ S) →
  ∀ c : HeckeCharacter ℚ, (∀ v ∉ S, IsUnramifiedChar (localChar c v)) → ∀ x h, IsUn S x h → ∀ s : ℂ, 1 < s.re → ∀ κ : KA,
    Ag (fun g => Wh φ g * conj (Wh φ (g * h))) c s κ.1 * partialLFunction (c * c) S (2 * s) =
      (∫ a : (InfiniteAdeleRing ℚ)ˣ, (fun y => Wh φ (realEmb y) * conj (Wh φ (realEmb y)))
          (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ) *
      (∏ v : S, Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v))) (localChar c v.1) s (finAt v.1 κ.1)) *
      ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s)

def E6 : Prop := ForE fun k N _ _ _ ω φ => ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ →
  ∀ (mK : Measure KA) [mK.IsHaarMeasure] [IsProbabilityMeasure mK] m, IsK m → ∀ γ, IsGauss γ → ∃ C : ℂ, C ≠ 0 ∧
  ∀ (S : Finset Pl), (∀ v, pOf v ∣ N → v ∈ S) → ∀ (c : HeckeCharacter ℚ) (δ : Bool), IsOfFinOrder c →
    (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) →
    ∀ x h, IsUn S x h → ∀ Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ, (∀ v, SB (Ψ v)) → ∀ s : ℂ, 1 < s.re →
      Jg mK (fun g => Wh φ g * conj (Wh φ (g * h))) c (tst γ S Ψ) s = C * (if δ then -1 else 1) * GG k s *
        ZS m μ₁ μ₂ φ₀ S x Ψ c s * ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s)

def G6 : Prop := ForE fun k N _ χ a _ φ => Pure k N χ a → ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ (S : Finset Pl), (∀ v, pOf v ∣ N → v ∈ S) →
  ∀ c : HeckeCharacter ℚ, IsOfFinOrder c → c ≠ 1 → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) → ∀ x h, IsUn S x h →
    ∫ g in 𝓕 ∩ band, φ g * conj (φ (g * h)) * cdet c g ∂μ ≠ 0 → Dih a

def X0 : Prop := ForE fun k N _ χ a ω φ => Pure k N χ a → ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ m, IsK m →
  ∀ (S : Finset Pl), (∀ v, pOf v ∣ N → v ∈ S) → ∀ (c : HeckeCharacter ℚ) (δ : Bool), IsOfFinOrder c →
    (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) →
    ∀ (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) → ∃ (C : ℂ) (E E' : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ E {s | 0 < s.re} ∧ DifferentiableOn ℂ E' {s | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → E s = (1 - 2 ^ (1 - s)) * (C * GG k s * ZS m μ₁ μ₂ φ₀ S x Ψ c s *
          ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s)) ∧
        E' s = (1 - 2 ^ (1 - s)) * (C * GG k s * ZS m μ₁ μ₂ φ₀ S x (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) c⁻¹ s *
          ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c⁻¹ v.1) s) * Lp c⁻¹ S s))) ∧
      (∀ s, Strip s → (1 - 2 ^ s) * E s = (1 - 2 ^ (1 - s)) * E' (1 - s)) ∧ (E 1 ≠ 0 → c ≠ 1 → Dih a)

def RealPlaceGammaFactors : Prop := ∀ (k : ℕ) (δ : Bool), 1 ≤ k → DifferentiableOn ℂ (GG k) {s | 0 < s.re} ∧ (∀ s : ℂ, 0 < s.re → GG k s ≠ 0) ∧
  DifferentiableOn ℂ (gamR k δ) {s | Strip s} ∧ ∀ s, Strip s →
    (-1) ^ k * GG k (1 - s) * Complex.Gammaℝ (s + if δ then 1 else 0) =
      gamR k δ s * GG k s * ((if δ then -Complex.I else 1) * Complex.Gammaℝ (1 - s + if δ then 1 else 0))

def HalfPlaneAnalyticIdentities : Prop := ∀ E Λ L Z P Q : ℂ → ℂ, DifferentiableOn ℂ E {s | 0 < s.re} → DifferentiableOn ℂ Λ {s | 1 / 4 < s.re} →
  Differentiable ℂ L → DifferentiableOn ℂ Z {s | 0 < s.re} →
  (∀ s : ℂ, 1 < s.re → E s = (1 - 2 ^ (1 - s)) * (Z s * (P s * Q s)) ∧ Λ s = (s - 1) ^ 1 * P s ∧ L s = (s - 1) * Q s) →
  (∀ s : ℂ, 1 / 4 < s.re → (s - 1) ^ 2 * E s = (1 - 2 ^ (1 - s)) * Z s * Λ s * L s) ∧
  (Z 1 ≠ 0 → (L 1 ≠ 0 → Λ 1 = 0) ∧ (L 1 = 0 → deriv L 1 ≠ 0 → E 1 = 0 → Λ 1 = 0))

def X1 : Prop := ForE fun k N _ χ a ω φ => Pure k N χ a → ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ D : Dat, D.k = k →
  (∀ v, D.ν v = μ₁ v * (μ₂ v)⁻¹) → (∀ v, v ∈ D.bad ↔ pOf v ∣ N) → FE a D

end Ad3.R

end
