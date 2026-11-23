import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec

def DSExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

def LowKMultOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → IsKTypeOf ε σ (lowK ε lam) S' → S = S'

def KTypesAbove : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b

def DSInfChar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → HasInfChar ε (fun a => (lam a : ℂ)) σ

def DSUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsHCParam lam → IsDS ε lam σ → IsDS ε lam σ' → UEquiv ε σ σ'

def DSExhaust : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ →
    ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), IsHCParam mu ∧
      (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
      IsDS (ε ∘ s) mu (fun g => σ (g.submatrix s.symm s.symm))

def DiscreteSpectrumKFiniteDecomposition : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε f → IsBiKFin ε f → IsZFinite ε f →
    MemLp (fun g : UJ ε => f (umat g)) 2 (muG ε) →
    ∃ (N : ℕ) (H : Fin N → Type) (_ : ∀ i, NormedAddCommGroup (H i)) (_ : ∀ i, InnerProductSpace ℂ (H i))
      (σ : ∀ i, Matrix (Fin n) (Fin n) ℂ → (H i →L[ℂ] H i)) (u v : ∀ i, H i),
      (∀ i, IsSqIntIrr ε (σ i) ∧ IsKFin ε (σ i) (u i) ∧ IsKFin ε (σ i) (v i)) ∧
      ∀ g ∈ UJset ε, f g = ∑ i, ⟪v i, σ i g (u i)⟫_ℂ

def ConvIdentity : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Wf : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)), FiniteDimensional ℂ Wf →
    (∀ f ∈ Wf, SmoothOnG ε f ∧ IsZFinite ε f ∧ ∀ k ∈ Kset ε, ∃ f' ∈ Wf, ∀ g ∈ UJset ε, f' g = f (g * k)) →
    ∀ U ∈ nhds (1 : UJ ε), ∃ β : Matrix (Fin n) (Fin n) ℂ → ℂ, SmoothOnG ε β ∧ HasCompactSupport (fun g : UJ ε => β (umat g)) ∧
      tsupport (fun g : UJ ε => β (umat g)) ⊆ U ∧
      ∀ f ∈ Wf, ∀ g : UJ ε, f (umat g) = ∫ y : UJ ε, f (umat (g * y⁻¹)) * β (umat y) ∂(muG ε)

def CartanInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (q : ℕ) (a b : Fin q → Fin n), q = rkR ε → Function.Injective a → Function.Injective b →
    (∀ i, ε (a i) = true ∧ ε (b i) = false) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ F : Matrix (Fin n) (Fin n) ℂ → ENNReal, Measurable (fun g : UJ ε => F (umat g)) →
      ∫⁻ g : UJ ε, F (umat g) ∂(muG ε) =
        c * ∫⁻ t in {t : Fin q → ℝ | Antitone t ∧ ∀ i, 0 ≤ t i},
          (∫⁻ k₁ : KG ε, ∫⁻ k₂ : KG ε,
            F (toMK k₁ * NormedSpace.exp (∑ i, (t i : ℂ) • (Matrix.single (a i) (b i) (1 : ℂ) + Matrix.single (b i) (a i) (1 : ℂ))) * toMK k₂)
              ∂(muK ε) ∂(muK ε)) *
          ENNReal.ofReal ((∏ i, ∏ j ∈ univ.filter (fun j => i < j), (Real.sinh (t i - t j) * Real.sinh (t i + t j)) ^ 2) *
            ∏ i, Real.sinh (2 * t i) * Real.sinh (t i) ^ (2 * (n - 2 * q)))

def PhiTri : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (c z c' : Matrix (Fin n) (Fin n) ℂ), IsLo c → IsUp c' → (∀ l, c l l ≠ 0 ∧ c' l l ≠ 0) → z ∈ Omega n →
    c * z * c' ∈ Omega n ∧ Phi lam (c * z * c') = (∏ l, (c l l * c' l l) ^ (-(muInt lam l))) * Phi lam z

def PhiPos : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (x : Matrix (Fin n) (Fin n) ℂ), x.PosDef → x ∈ Omega n ∧ 0 < Phi lam x ∧
    (∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ) ∧
    ∀ b : Matrix (Fin n) (Fin n) ℂ, IsLo b → x = b * bᴴ → Phi lam x = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ)

def PhiEigen : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), IsHCParam lam → ∀ (k z : Matrix (Fin n) (Fin n) ℂ), IsUnit k → k⁻¹ * z * k ∈ Omega n → ∀ m : ℕ,
    gelfH m (fun y => Phi lam (k⁻¹ * y * k)) z = gelfVal (fun a => -(lam a : ℂ)) (m + 1) * Phi lam (k⁻¹ * z * k)

def TauExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (w : S),
    IsURepOn (Kset ε) σ → IsKTypeOf ε σ abelian₂ S → ‖w‖ = 1 → IsWtOn (Kset ε) σ abelian₂ (w : H) →
    ∃ τ : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S), IsTau ε abelian₂ τ w ∧ ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v

def PsBasic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    IsOpen {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} ∧ (∀ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef → x ∈ U1 ε) ∧
    DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z)) {z | Matrix.of z ∈ U1 ε} ∧
    ps ε lam τ w 1 = ContinuousLinearMap.id ℂ W

def IwasawaKC : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ κ β : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    (∀ y ∈ KC ε, κ y ∈ Kset ε ∧ β y ∈ KC ε ∧ IsLo (β y) ∧ (∀ l, 0 < β y l l) ∧ y = κ y * β y) ∧
    ContinuousOn κ (KC ε) ∧ ContinuousOn β (KC ε) ∧
    ∀ k ∈ Kset ε, ∀ b ∈ KC ε, IsLo b → (∀ l, 0 < b l l) → κ (k * b) = k ∧ β (k * b) = b

def IwasawaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) (κ β : KG ε → Matrix (Fin n) (Fin n) ℂ), y ∈ KC ε →
    (∀ k, κ k ∈ Kset ε ∧ β k ∈ KC ε ∧ IsLo (β k) ∧ (∀ l, 0 < β k l l) ∧ y * toMK k = κ k * β k) →
    ∀ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn F (Kset ε) →
      ∫ k, F (κ k) * ((∏ l, ‖β k l l‖ ^ (4 * rhoC ε l) : ℝ) : ℂ) ∂(muK ε) = ∫ k, F (toMK k) ∂(muK ε)

def PsEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    ∀ x y : Matrix (Fin n) (Fin n) ℂ, x.PosDef → y ∈ KC ε →
      ps ε lam τ w (y * x * yᴴ) = (τ y).comp ((ps ε lam τ w x).comp (τ yᴴ))

def PsiPolar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    (∀ k ∈ Kset ε, ∀ X, inP ε X → Psi ε lam τ w (k * NormedSpace.exp X) = (τ k).comp (ps ε lam τ w (NormedSpace.exp X))) ∧
    Psi ε lam τ w 1 = ContinuousLinearMap.id ℂ W ∧
    ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, ∀ g ∈ UJset ε,
      Psi ε lam τ w (k₁ * g * k₂) = (τ k₁).comp ((Psi ε lam τ w g).comp (τ k₂))

def PsLocal : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    ∀ᶠ g : UJ ε in nhds 1, umat g ∈ U1 ε ∧ Psi ε lam τ w (umat g) = ps ε lam τ w (umat g)

def PsiAnalytic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    ∀ u v : W, ∀ g ∈ UJset ε, ∃ F : (Fin n → Fin n → ℂ) → ℂ, AnalyticAt ℝ F (fun i j => g i j) ∧
      ∀ᶠ z : Fin n → Fin n → ℂ in nhds (fun i j => g i j), Matrix.of z ∈ UJset ε →
        ⟪u, Psi ε lam τ w (Matrix.of z) v⟫_ℂ = F z

def PsiEigen : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    ∀ u v : W, SmoothOnG ε (fun g => ⟪u, Psi ε lam τ w g v⟫_ℂ) ∧
      IsZEigen ε (fun a => -(lam a : ℂ)) (fun g => ⟪u, Psi ε lam τ w g v⟫_ℂ)

def PsiDecay : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w →
    ∀ h : ℝ, GapAtLeast ε lam h → ∀ k ∈ Kset ε, ∀ X, inP ε X →
      ‖Psi ε lam τ w (k * NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X))

def MajInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (h r s : ℝ), 0 < r → 0 ≤ s →
    16 * n * rkR ε / r + 8 * s * Real.sqrt (2 * rkR ε) / r < h →
    ∀ f : Matrix (Fin n) (Fin n) ℂ → ℝ, Measurable (fun g : UJ ε => f (umat g)) →
      (∀ k ∈ Kset ε, ∀ X, inP ε X → |f (k * NormedSpace.exp X)| ≤ decHS h (rkR ε) (Real.sqrt (hs X))) →
      Integrable (fun g : UJ ε => |f (umat g)| ^ r * Real.exp (s * dOp (umat g))) (muG ε)

def IdentDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsSqIntIrr ε σ →
    HasInfChar ε (fun a => (lam a : ℂ)) σ → (∃ S, IsKTypeOf ε σ (lowK ε lam) S) → IsDS ε lam σ

def GelfSep : Prop :=
  ∀ (n : ℕ) (χ χ' : Fin n → ℂ), (∀ k, gelfVal χ k = gelfVal χ' k) ↔ ∃ s : Equiv.Perm (Fin n), χ' = χ ∘ s

def SpanEnd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), CompleteSpace H → IsURepOn (UJset ε) σ →
    IsIrredOn (UJset ε) σ → IsKTypeOf ε σ abelian₂ S → (∀ S', IsKTypeOf ε σ abelian₂ S' → S' = S) →
    ∀ (m : ℕ) (u v : Fin m → S), (∀ g ∈ UJset ε, ∑ i, ⟪(v i : H), σ g (u i)⟫_ℂ = 0) →
      ∀ A : S →L[ℂ] S, ∑ i, ⟪v i, A (u i)⟫_ℂ = 0

def FormulaF : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 8 * n * rkR ε < h → ∀ w, IsHighestUnit ε lam σ w →
    ∀ k ∈ Kset ε, ∀ X, inP ε X → ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ⟪v, σ (k * NormedSpace.exp X) u⟫_ℂ = (Module.finrank ℂ (lowKSub ε lam σ) : ℂ) *
        ∫ k' : KG ε, Phi lam ((toMK k')⁻¹ * NormedSpace.exp X * toMK k') *
          (⟪v, σ (k * toMK k') w⟫_ℂ * ⟪σ (toMK k') w, u⟫_ℂ) ∂(muK ε)

def FPlus : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 8 * n * rkR ε < h → ∀ X, inP ε X → ∀ u ∈ lowKSub ε lam σ,
      0 ≤ ⟪u, σ (NormedSpace.exp X) u⟫_ℂ

def Dec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 8 * n * rkR ε < h → ∀ k ∈ Kset ε, ∀ X, inP ε X →
    ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ‖⟪v, σ (k * NormedSpace.exp X) u⟫_ℂ‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖v‖

def DFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (∀ g ∈ UJset ε, 0 ≤ dOp g ∧ dOp g⁻¹ = dOp g ∧
      (∀ g' ∈ UJset ε, dOp (g * g') ≤ dOp g + dOp g') ∧ ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, dOp (k₁ * g * k₂) = dOp g) ∧
    ContinuousOn dOp (UJset ε) ∧
    ∀ k ∈ Kset ε, ∀ X, inP ε X → dHS (k * NormedSpace.exp X) = Real.sqrt (hs X) ∧
      Real.sqrt 2 * dOp (k * NormedSpace.exp X) ≤ Real.sqrt (hs X) ∧
      Real.sqrt (hs X) ≤ Real.sqrt (2 * rkR ε) * dOp (k * NormedSpace.exp X)

def DecOp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 8 * n * rkR ε < h → ∀ g ∈ UJset ε,
    ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ, ‖⟪v, σ g u⟫_ℂ‖ ≤ decE (rkR ε) h (dOp g) * ‖u‖ * ‖v‖

def MajIntOp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 8 * Real.sqrt (rkR ε) * (s + 2 * n * rkR ε) < h →
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (umat g)) * Real.exp (s * dOp (umat g))) (muG ε)

def DecAll : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 8 * n * rkR ε < h → ∀ u u' : H, IsKFin ε σ u → IsKFin ε σ u' →
      (∀ r₀ : ℝ, 0 < r₀ → ∃ C : ℝ, ∀ g ∈ UJset ε,
        ‖⟪u', σ g u⟫_ℂ‖ ≤ C * decE (rkR ε) h (max 0 (dOp g - 2 * r₀))) ∧
      ∃ C' : ℝ, ∀ g ∈ UJset ε, ‖⟪u', σ g u⟫_ℂ‖ ≤ C' * Real.exp (-(h / (8 * Real.sqrt (rkR ε))) * dOp g)

def CoefficientWeightedIntegrable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h s : ℝ, GapAtLeast ε lam h → 0 ≤ s → 16 * n * rkR ε + 8 * s * Real.sqrt (2 * rkR ε) < h →
    ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      Integrable (fun g : UJ ε => ‖⟪v, σ (umat g) u⟫_ℂ‖ * Real.exp (s * dOp (umat g))) (muG ε)

end GlobalTheory.Dec
