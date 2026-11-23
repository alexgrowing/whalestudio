import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def em (h : GL (Fin 2) F) : GL (Fin 3) F :=
  if hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

def tinv {n : Type} [Fintype n] [DecidableEq n] (g : GL n F) : GL n F :=
  ⟨(g⁻¹ : GL n F).valᵀ, g.valᵀ, by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

def w2 : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
def w3 : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def dW3 (W : GL (Fin 3) F → ℂ) (g : GL (Fin 3) F) : ℂ := W (w3 * tinv g)
def dW2 (W : GL (Fin 2) F → ℂ) (h : GL (Fin 2) F) : ℂ := W (w2 * tinv h)

variable (F) in

def K2 : Set (GL (Fin 2) F) := (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))

def mIw (ψ : AddChar F Circle) : Measure (Fˣ × Fˣ × GL (Fin 2) F) :=
  (multHaar F).prod ((multHaar F).prod ((LFS.hG ψ).restrict (K2 F)))

def iw (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (s : ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℂ :=
  W (em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1)

def zetaGL3GL2 (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (s : ℂ) : ℂ := ∫ p, iw W W' s p ∂mIw ψ

structure WhT (χ : AddChar F Circle) (ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)) : Prop where
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x g, W (uni2 x * g) = (χ x : ℂ) * W g
  cen : ∀ W ∈ V, ∀ (a : Fˣ) g, W (dg2 a a * g) = ((ω a : ℂˣ) : ℂ) * W g
  smooth : ∀ W ∈ V, ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  bound : ∀ W ∈ V, ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)
  fe : ∀ W ∈ V, ∀ c, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun a => W (dg2 a 1 * w0) * (((ω a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) (multHaar F) ∧
    Integrable (fun a => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
    ∫ a, W (dg2 a 1 * w0) * (((ω a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
      G c s * ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def FunctionalEquationPair (ψ : AddChar F Circle) (ν ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ) (W : GL (Fin 3) F → ℂ)
    (W' : GL (Fin 2) F → ℂ) (s : ℂ) : Prop :=
  Integrable (iw W W' s) (mIw ψ) ∧ Integrable (iw (dW3 W) (dW2 W') (1 - s)) (mIw ψ) ∧
    zetaGL3GL2 ψ (dW3 W) (dW2 W') (1 - s) = ((ω (-1) : ℂˣ) : ℂ) * G ν s * G 1 s * G ν⁻¹ s * zetaGL3GL2 ψ W W' s

end D

def LocalFunctionalEquationFinite : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν →
    ∀ ω G V', IsUnit1 ω → WhT ψ⁻¹ ω G V' → ∀ W ∈ LFS.VF ψ (V2 ψ ν ν⁻¹), ∀ W' ∈ V', ∀ s : ℂ, 0 < s.re → s.re < 1 →
      FunctionalEquationPair ψ ν ω G W W' s

section W

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

open Classical in
variable (E) in

def nsg (a : F) : ℂ := if ∃ t : Eˣ, Algebra.norm F (t : E) = a then 1 else -1

open Classical in

def rW (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d : F) (Φ : E → ℂ) (z : E) : ℂ :=
  if c = 0 then (χ (a * b * Algebra.norm F z) : ℂ) * nsg E a * ((modulus a : ℝ) : ℂ) * Φ (algebraMap F E a * z)
  else lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
    ∫ u, (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * Φ u ∂μE

open Classical in

def Wc (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ) (g : GL (Fin 2) F) : ℂ :=
  if h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det then
    ((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ μE lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun x => Φ (x * (h.choose : E))) 1
  else 0

variable (F E) in

def SBc (c : Eˣ →* ℂˣ) : Set (E → ℂ) :=
  {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
    ∀ u : Eˣ, Algebra.norm F (u : E) = 1 → ∀ x, Φ (x * u) = (((c u)⁻¹ : ℂˣ) : ℂ) * Φ x}

def VW (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) F → ℂ) :=
  Submodule.span ℂ {W | ∃ Φ ∈ SBc F E c, ∃ h₀ : GL (Fin 2) F, W = fun g => Wc χ σ μE lam c Φ (g * h₀)}

def resF (c : Eˣ →* ℂˣ) : Fˣ →* ℂˣ := c.comp (Units.map (algebraMap F E).toMonoidHom)

def viaN (μ : Fˣ →* ℂˣ) : Eˣ →* ℂˣ := μ.comp (Units.map (Algebra.norm F : E →* F))

end W

section WF

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

variable (E) in

def chE (χ : AddChar F Circle) : AddChar E Circle := χ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

variable (E) in

def lamE (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) : ℂ := gam χ 1 (1 / 2) * gam χ η (1 / 2) / gam (chE E χ) 1 (1 / 2)

end WF

def WeilJLF : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 →
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
      [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) →
    ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) →
    ∀ c : Eˣ →* ℂˣ, IsUnit1 c →
      WhT χ (resF c * η) (fun μ s => lamE E χ η * gam (chE E χ) (c * viaN μ) s)
        (VW χ σ (selfDualMeasure (chE E χ)) (lamE E χ η) c)

def swapE {F : Type} [Field F] : (F × F) ≃ₐ[F] (F × F) := AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl)

def cS {F : Type} [Field F] (c₁ c₂ : Fˣ →* ℂˣ) : (F × F)ˣ →* ℂˣ := (c₁.coprod c₂).comp MulEquiv.prodUnits.toMonoidHom

def WcS {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (g : GL (Fin 2) F) : ℂ :=
  ((c₁ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2) *
    ∫ u : Fˣ, rW χ swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) *
      ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F

def VWS {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) F → ℂ) :=
  Submodule.span ℂ {W | ∃ Φ : F × F → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧ ∃ h₀ : GL (Fin 2) F,
    W = fun g => WcS χ c₁ c₂ Φ (g * h₀)}

def WeilJLS : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ →
      WhT χ (c₁ * c₂) (fun μ s => gam χ (c₁ * μ) s * gam χ (c₂ * μ) s)
        (VWS χ c₁ c₂)

section R

open Classical in

def emR (h : GL (Fin 2) ℝ) : GL (Fin 3) ℝ :=
  if hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

def tinvR {n : Type} [Fintype n] [DecidableEq n] (g : GL n ℝ) : GL n ℝ :=
  ⟨(g⁻¹ : GL n ℝ).valᵀ, g.valᵀ, by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

def w2R : GL (Fin 2) ℝ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
def w3R : GL (Fin 3) ℝ :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def dW3R (W : GL (Fin 3) ℝ → ℂ) (g : GL (Fin 3) ℝ) : ℂ := W (w3R * tinvR g)
def dW2R (W : GL (Fin 2) ℝ → ℂ) (h : GL (Fin 2) ℝ) : ℂ := W (w2R * tinvR h)

open Classical in

def rotR (θ : ℝ) : GL (Fin 2) ℝ :=
  if hd : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

def kR (θ : ℝ) (ε : Bool) : GL (Fin 2) ℝ := rotR θ * (if ε then dg2 1 (-1) else 1)

def iwR (W : GL (Fin 3) ℝ → ℂ) (W' : GL (Fin 2) ℝ → ℂ) (s : ℂ) (ε : Bool) (p : ℝˣ × ℝˣ × ℝ) : ℂ :=
  W (emR (dg2 (p.1 * p.2.1) p.2.1 * kR p.2.2 ε)) * W' (dg2 (p.1 * p.2.1) p.2.1 * kR p.2.2 ε) *
    chR false (s - 3 / 2) p.1 * chR false (2 * s - 1) p.2.1

def mIwR : Measure (ℝˣ × ℝˣ × ℝ) := mulR.prod (mulR.prod (volume.restrict (Set.Ioc 0 (2 * Real.pi))))

def realZetaIntegralGL3GL2 (W : GL (Fin 3) ℝ → ℂ) (W' : GL (Fin 2) ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ p, iwR W W' s false p ∂mIwR + ∫ p, iwR W W' s true p ∂mIwR

def WthR (n : ℤ) (g : GL (Fin 2) ℝ) : ℂ :=
  if 0 < (g.val).det then
    (((g.val).det : ℝ) : ℂ) ^ (((n.natAbs + 1 : ℕ) : ℂ) / 2) *
      ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
      Complex.exp (2 * Real.pi * Complex.I * (((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) /
        ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ))))
  else 0

def archimedeanGammaFactorGL3GL2 (k : ℕ) (n : ℤ) (s : ℂ) : ℂ :=
  Complex.Gammaℂ (s + (n + 2 * (k - 1 : ℕ)).natAbs / 2) * Complex.Gammaℂ (s + n.natAbs / 2) *
    Complex.Gammaℂ (s + (n - 2 * (k - 1 : ℕ)).natAbs / 2)

def eR (k : ℕ) (n : ℤ) : ℂ :=
  Complex.I * (-Complex.I) ^ ((n + 2 * (k - 1 : ℕ)).natAbs + n.natAbs + (n - 2 * (k - 1 : ℕ)).natAbs)

end R

def LocalFunctionalEquationReal : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∃ W ∈ Submodule.span ℂ (Set.range (LR.sec k)), ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ,
    (0 < s.re → (∀ ε, Integrable (iwR W (WthR n) s ε) mIwR) ∧ realZetaIntegralGL3GL2 W (WthR n) s = C * archimedeanGammaFactorGL3GL2 k n s) ∧
    (0 < s.re → (∀ ε, Integrable (iwR (dW3R W) (dW2R (WthR n)) s ε) mIwR) ∧
      realZetaIntegralGL3GL2 (dW3R W) (dW2R (WthR n)) s = eR k n * C * archimedeanGammaFactorGL3GL2 k n s)

end Ad3.K.GL2LocalData
