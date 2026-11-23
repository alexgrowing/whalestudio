import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsStableSquareIntegrableForms

noncomputable section

open NumberField MeasureTheory ComplexConjugate
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def GrowP (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∀ ε : ℝ, 0 < ε → An.Bnd f fun r => An.rho E N r + ε

def GrowQ (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∃ κ : ℕ → ℝ, (∀ r, 0 < r → r < N → κ r < An.rho E N r) ∧ An.Bnd f κ

def pr (f g : GA E N → ℂ) : ℂ := pet (latticeGL E N) (Measure.haar : Measure (GA E N)) f g

end Defs

def GrowPHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (χ : Sm E N),
  IsAutForm χ → (∀ (t : ℝ) g, χ.1 (splitCentre E N t * g) = χ.1 g) →
  (∀ r, 0 < r → r < N → ∀ c ∈ Exp r χ.1, pE E N r c ≤ 0) → GrowP χ.1

def GrowQHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (u : Sm E N),
  IsAutForm u → IsSqInt u.1 → GrowQ u.1

def IntBnd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (H : GA E N → ℝ),
  Continuous H → (∀ g, 0 ≤ H g) → (∀ γ ∈ latticeGL E N, ∀ g, H (γ * g) = H g) →
  ∀ m : ℕ → ℝ, (∀ r, 0 < r → r < N → m r < 2 * An.rho E N r) → An.Bnd (fun g => (H g : ℂ)) m →
    ∫⁻ g in stdDom (latticeGL E N), ENNReal.ofReal (H g) ∂(Measure.haar : Measure (GA E N)) < ⊤

def PairLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ),
  (∀ (f₁ f₂ g : GA E N → ℂ) (c : ℂ), GrowP f₁ → GrowP f₂ → GrowQ g →
    pr (f₁ + f₂) g = pr f₁ g + pr f₂ g ∧ pr (c • f₁) g = c * pr f₁ g) ∧
  ∀ (f g₁ g₂ : GA E N → ℂ) (c : ℂ), GrowP f → GrowQ g₁ → GrowQ g₂ →
    pr f (g₁ + g₂) = pr f g₁ + pr f g₂ ∧ pr f (c • g₁) = conj c * pr f g₁

def PairRt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (x : GA E N)
  (f g : GA E N → ℂ), (∀ γ ∈ latticeGL E N, ∀ y, f (γ * y) = f y) → (∀ γ ∈ latticeGL E N, ∀ y, g (γ * y) = g y) →
    pr (fun y => f (y * x)) g = pr f (fun y => g (y * x⁻¹))

def PairLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (X : Lie E N)
  (χ u : Sm E N), GrowP χ.1 → GrowP (act (.lie X) χ).1 → GrowQ u.1 → GrowQ (act (.lie X) u).1 →
    pr (act (.lie X) χ).1 u.1 = -pr χ.1 (act (.lie X) u).1

def Core : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (U : Submodule ℂ (Sm E N)),
  IsStable U → (∀ χ ∈ U, IsAutForm χ) → (∀ χ ∈ U, GrowP χ.1) → ∀ φ ∈ U, φ ∈ A2 E N → φ ≠ 0 →
    ∃ (V : Submodule ℂ (Sm E N)) (p : Sm E N →ₗ[ℂ] Sm E N), IsDiscrete V ∧ (∀ χ ∈ U, p χ ∈ V) ∧
      (∀ o, ∀ χ ∈ U, p (act o χ) = act o (p χ)) ∧ p φ ≠ 0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
