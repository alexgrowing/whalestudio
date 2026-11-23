import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec

def AutFinite : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g →
    ∀ (N : InfinitePlace I.F → ℕ → ℕ) (c : ∀ v m, Fin (N v m) → ℂ)
      (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (τ : Kinf I → (W →L[ℂ] W)),
      IsURep τ →
      FiniteDimensional ℂ (Submodule.span ℂ {f : I.GA → ℂ | IsSmoothMG I g f ∧
        (∀ v m x, (zOp I v m)^[N v m] f x = ∑ i, c v m i * (zOp I v m)^[i.val] f x) ∧
        ∃ L : W →ₗ[ℂ] (I.GA → ℂ), (∀ (k : Kinf I) w x, L (τ k w) x = L w (x * (fun v => (k v : UJ (I.ε v)), 1))) ∧
          f ∈ LinearMap.range L})

def CoefCusp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ u v : H, IsKFin ε σ u → IsKFin ε σ v →
    ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
      Integrable (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) ν ∧ ∫ m, ⟪v, σ (umat (x * m * y)) u⟫_ℂ ∂ν = 0

def ProjAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ x, Continuous fun g => σ g x) →
    ∀ d : ℝ, 0 < d →
    (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) →
    ∀ w : H, ‖w‖ = 1 → Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ →
      (∀ g : G, star (phG d σ w g⁻¹) = phG d σ w g) ∧
      (∀ x y : G, ∫ g, phG d σ w g * phG d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phG d σ w y) ∧
      ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
        (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) →
        (∃ P : Hp →L[ℂ] Hp, IsOpIntG μ π (phG d σ w) P) ∧
        ∀ P : Hp →L[ℂ] Hp, IsOpIntG μ π (phG d σ w) P →
          IsStarProjection P ∧
          (∀ x : G, P ∘L π x ∘L P = ⟪w, σ x w⟫_ℂ • P) ∧
          (∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
            (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
            ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u)) ∧
          ((LinearMap.range (P : Hp →ₗ[ℂ] Hp) : Submodule ℂ Hp) : Set Hp) =
            {v | ∃ io : H →L[ℂ] Hp, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w}

def TensorRep : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    IsURep B.σs ∧ IsIrr B.σs ∧ IsFdegG (muInf B.I) B.σs (∏ v, d v) ∧ ‖B.tens B.w‖ = 1 ∧
      ∀ g, ph B d g = ((∏ v, d v : ℝ) : ℂ) * star ⟪B.tens B.w, B.σs g (B.tens B.w)⟫_ℂ

def PhMaj : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h →
    Continuous (ph B d) ∧ (∀ g, ‖ph B d g‖ ≤ majPh B d h g) ∧
    ∀ s : ℝ, 0 ≤ s → (∀ v, rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h) →
      Integrable (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) (muInf B.I)

def GlobalProj : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Integrable (ph B d) (muInf B.I) →
    IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧
    (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧
    (∃ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T) ∧
    ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
      IsOrthProjOnto T (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧
      (∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, T (A (B.tens B.w)) = A (B.tens B.w)) ∧
      (∀ y, T y = y → ∃! A, A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re ∧ A (B.tens B.w) = y) ∧
      (FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund))) ∧
      Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D

def CountRat : Prop :=
  ∀ (I : AutInst) (x y : I.GA) (r : InfinitePlace I.F → ℝ), 1 ≤ I.n → (∀ v, 0 ≤ r v) →
    {γ ∈ I.GFset | (x⁻¹ * γ * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v}.Finite ∧
    (({γ ∈ I.GFset | (x⁻¹ * γ * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
      (3 * Real.sqrt I.n / (tau1 I x * tau1 I y)) ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

def TauLip : Prop :=
  ∀ I : AutInst, 1 ≤ I.n → (∀ x, 0 < tau1 I x) ∧ Continuous (tau1 I) ∧ (∀ γ ∈ I.GFset, ∀ x, tau1 I (γ * x) = tau1 I x) ∧
    ∀ x g : I.GA, g.2 ∈ I.Kset → |Real.log (tau1 I (x * g)) - Real.log (tau1 I x)| ≤ dSum I g.1 / I.f

def ConvolutionSmoothL2 : Prop :=
  ∀ (B : RowsAut) (g : ℕ), 1 ≤ B.I.n → 1 ≤ g → ∀ a : B.I.Ginf → ℂ, SmoothInf B.I a → HasCompactSupport a →
    ∃ C : ℝ, ∀ y : B.I.L2 B.μf B.fund, (∀ k ∈ B.I.Kg g, B.R (1, k) y = y) →
      ∀ T, IsOpOf (muInf B.I) (fun x => B.R (x, 1)) a T →
        ∃ f : B.I.GA → ℂ, IsSmoothMG B.I g f ∧ Continuous f ∧
          (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖y‖) ∧
          (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] f

def RowsFinite : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)

def KernelA : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h →
    (∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧
      ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤
        kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧
    Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) ∧
    (∀ γ ∈ B.I.GFset, ∀ x y, kern B.I (phe B d) (γ * x) y = kern B.I (phe B d) x y ∧
      kern B.I (phe B d) x (γ * y) = kern B.I (phe B d) x y) ∧
    ∀ x y, kern B.I (phe B d) y x = star (kern B.I (phe B d) x y)

def KernelB : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
    ∃ (y : Fin B.D → B.I.L2 B.μf B.fund) (Fc : Fin B.D → B.I.GA → ℂ), Orthonormal ℂ y ∧
      Submodule.span ℂ (Set.range y) = LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund) ∧
      (∀ i, Continuous (Fc i) ∧ (∀ γ ∈ B.I.GFset, ∀ x, Fc i (γ * x) = Fc i x) ∧
        (y i : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] Fc i) ∧
      (∀ x z, kern B.I (phe B d) x z = ∑ i, Fc i x * star (Fc i z)) ∧
      IntegrableOn (fun x => kern B.I (phe B d) x x) B.fund (B.I.muA B.μf) ∧
      ∫ x in B.fund, kern B.I (phe B d) x x ∂(B.I.muA B.μf) = (B.D : ℂ) ∧
      ∀ (c : Fin B.D → ℂ) (x : B.I.GA), ‖∑ i, c i * Fc i x‖ ^ 2 ≤
        (∑ i, ‖c i‖ ^ 2) * (kerC B d * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f))

def WeilVanish : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G),
    IsClosed (N : Set G) → IsHaarSub (N : Set G) ν →
    ∀ F φ : G → ℂ, Measurable F → Measurable φ → (∀ m ∈ N, ∀ y, F (m * y) = F y) →
      Integrable (fun y => F y * φ y) μ → (∀ y, ∫ m, φ (m * y) ∂ν = 0) →
      ∫ y, F y * φ y ∂μ = 0

def CuspCont : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → HBig B 40 h →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
    ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B (T y) f →
      ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0

def Cuspidal : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → HBig B 40 h →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T →
    ∀ y, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y))

def NearUnip : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (c : ℝ), 0 < c → c ≤ 1 / 10 ^ 5 → 1 ≤ B.I.n →
    4 * B.I.n < B.g₀ →
    (Ideal.span {(B.g₀ : 𝓞 B.I.E)}).IsRadical →
    ∀ ep δ : ℝ, ep = c / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) → δ = 3 * Real.sqrt (B.I.n * ep) →
      (∀ x γ : B.I.GA, IsNear B d ep x γ →
        (B.I.fmat γ.2 - 1) ^ B.I.n = 0 ∧ (∀ v, (uMat (γ.1 v) - 1) ^ B.I.n = 0) ∧ γ ∈ nearSet B.I x δ) ∧
      δ < 1 / 4 ∧ ∀ q : ℕ, q ^ 2 ≤ B.I.n → δ * q * B.I.n * B.I.f ≤ 1 / 100

end GlobalTheory.Dec
