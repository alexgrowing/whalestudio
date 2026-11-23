import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics

structure GDatum (D : ℕ) : Type 1 where

  Ω : Type
  [fieldΩ : Field Ω]
  [charΩ : CharZero Ω]

  κ : Type
  [fintypeκ : Fintype κ]

  x : Ix κ → Ω

  m : ConeMetric ℂ (Ix κ)

  μ : Measure (Ix κ → ℂ)
  good : IsGood D x m μ

attribute [instance] GDatum.fieldΩ GDatum.charΩ GDatum.fintypeκ

def IsInvMat {J : Type} [Fintype J] (A : Matrix J J ℚ) : Prop :=
  ∃ B : Matrix J J ℚ, ∀ v : J → ℚ, A.mulVec (B.mulVec v) = v ∧ B.mulVec (A.mulVec v) = v

def IsTransport {κ : Type} [Fintype κ] (A : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ))
    (μ μ' : Measure (Ix κ → ℂ)) : Prop :=
  (∀ z, m'.ρ (matActC A z) = m.ρ z) ∧ μ' = μ.map (matActC A)

def IsPullFS {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ} (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)) : Prop :=
  ∀ z ∈ pts (coordIdeal ℤ x), m.ρ z = Real.sqrt (∑ k, ‖z (e k)‖ ^ 2)

def hhOf (I : AllFam) (D : ℕ) : ℝ :=
  I Unit (GlobalTheory (Fin (D + 1))) ⊥ (D + 1) fun _ => HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))

abbrev pw (D : ℕ) : ℕ → ℝ := fun n => (n : ℝ) ^ (D + 1)

def StepA (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m₀ m₁ : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e → IsGood D x m₀ μ → IsGood D x m₁ μ →
    (fun n => defect I D x m₁ μ n - defect I D x m₀ μ n) =o[atTop] pw D

def StepT (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (A : Matrix (Ix κ) (Ix κ) ℚ)
    (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsInvMat A → IsProjFrame (matAct A x) e →
    ∃ m' μ', IsTransport A m m' μ μ' ∧ IsGood D (matAct A x) m' μ'

def StepB (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m m' : ConeMetric ℂ (Ix κ)) (μ μ' : Measure (Ix κ → ℂ)) (A : Matrix (Ix κ) (Ix κ) ℚ)
    (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsInvMat A → IsProjFrame (matAct A x) e → IsTransport A m m' μ μ' →
    IsGood D (matAct A x) m' μ' →
    (fun n => defect I D (matAct A x) m' μ' n - defect I D x m μ n) =o[atTop] pw D

def StepN (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)), IsGood D x m μ →
    ∃ (A : Matrix (Ix κ) (Ix κ) ℚ) (e : Fin (D + 1) → Ix κ),
      IsInvMat A ∧ IsProjFrame (matAct A x) e

def StepM (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsProjFrame x e → ∃ m₀, IsPullFS x e m₀ ∧ IsGood D x m₀ μ

def StepC (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsProjFrame x e → IsPullFS x e m →
    (fun n => defect I D x m μ n - (projDeg x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =o[atTop] pw D

def StepV (I : AllFam) (D : ℕ) : Prop :=
  ∃ d : GDatum D, (∀ n, chi d.x d.m d.μ n = chiP D (2 * n)) ∧
    top I d.x d.m D = 2 ^ (D + 1) * hhOf I D ∧
    ∀ (A : Matrix (Ix d.κ) (Ix d.κ) ℚ) (e : Fin (D + 1) → Ix d.κ), IsInvMat A →
      IsProjFrame (matAct A d.x) e → projDeg (matAct A d.x) e = 2 ^ D

theorem exists_projDeg_defect (I : AllFam) (D : ℕ) (hA : StepA I D) (hT : StepT D)
    (hB : StepB I D) (hN : StepN D) (hM : StepM D) (hC : StepC I D) (d : GDatum D) :
    ∃ (A : Matrix (Ix d.κ) (Ix d.κ) ℚ) (e : Fin (D + 1) → Ix d.κ), IsInvMat A ∧
      IsProjFrame (matAct A d.x) e ∧
      (fun n => defect I D d.x d.m d.μ n -
        (projDeg (matAct A d.x) e : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D := by
  obtain ⟨A, e, hAinv, hPF⟩ := hN d.Ω d.κ d.x d.m d.μ d.good
  obtain ⟨m', μ', hTr, hG'⟩ := hT d.Ω d.κ d.x d.m d.μ A e d.good hAinv hPF
  obtain ⟨m₀, hPull, hG₀⟩ := hM d.Ω d.κ (matAct A d.x) m' μ' e hG' hPF
  refine ⟨A, e, hAinv, hPF, ?_⟩
  have h1 := hC d.Ω d.κ (matAct A d.x) m₀ μ' e hG₀ hPF hPull
  have h2 := hA d.Ω d.κ (matAct A d.x) m₀ m' μ' e hPF hG₀ hG'
  have h3 := hB d.Ω d.κ d.x d.m m' d.μ μ' A e d.good hAinv hPF hTr hG'
  refine ((h1.add h2).sub h3).congr_left (fun n => ?_)
  ring

theorem hs_of_steps (I : AllFam) (D : ℕ) (hA : StepA I D) (hT : StepT D) (hB : StepB I D)
    (hN : StepN D) (hM : StepM D) (hC : StepC I D) (hV : StepV I D) (d : GDatum D) :
    defect I D d.x d.m d.μ =o[atTop] pw D := by
  obtain ⟨d₂, hchi, htop, hdeg⟩ := hV
  have hH : hsDefect D (chiP D) (hhOf I D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    apply hilbertSamuelDefect_projectiveSpace_isLittleO
    obtain ⟨A, e, hAi, hPF, hlo⟩ := exists_projDeg_defect I D hA hT hB hN hM hC d₂
    rw [hdeg A e hAi hPF] at hlo
    have hc : chi d₂.x d₂.m d₂.μ = fun m => chiP D (2 * m) := funext hchi
    simp only [defect, hc, htop] at hlo
    push_cast at hlo
    exact hlo
  obtain ⟨A, e, -, -, hlo⟩ := exists_projDeg_defect I D hA hT hB hN hM hC d
  refine (hlo.add (hH.const_mul_left (projDeg (matAct A d.x) e : ℝ))).congr_left (fun n => ?_)
  ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
