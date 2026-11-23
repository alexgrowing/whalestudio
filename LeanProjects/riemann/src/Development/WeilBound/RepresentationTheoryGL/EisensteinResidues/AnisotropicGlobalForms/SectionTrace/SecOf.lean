import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

abbrev UD (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) : Type := (adCM D.sp.cm.sig χ).U (-1) (Fin n)

def TStd : Prop := Dict → DictInf →
  ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), ∃ Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n,
    (∀ g, g ∈ GlobalTheory.StdUnn.GF D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uΓ (-1) (Fin n)) ∧
    (∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ∧
    (∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n)) ∧
    ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Ψ g).1 = Matrix.GeneralLinearGroup.det a

def Chart : Prop :=
  ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a →
    ∃ (Φ : GA D (dblSp V) ≃ₜ* UD D χ V.rank) (p : siegel V),
    (∀ g, g ∈ GQ (dblSp V) ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uΓ (-1) (Fin V.rank)) ∧
    (∀ g, g ∈ siegel V ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ∧
    (∀ k, k ∈ Khat V a ↔ Φ ((p : GA D (dblSp V))⁻¹ * k * p) ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) ∧
    (∀ q : siegel V, bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) (Φ q).1 = aP V q) ∧
    ∀ x : (AE D)ˣ, (adCM D.sp.cm.sig χ).lg x = Real.log (absA D x)

def TChart : Prop := Dict → DictInf → TStd → Chart

def Scal : Prop :=
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [T2Space G'] [LocallyCompactSpace G'] (Φ : G ≃ₜ* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ)
    (N : ℝ), IsCompact (K' : Set G') → IsPar Γ' K' P' c → IsHt Γ' K' P' η → (∀ g, g ∈ Γ ↔ Φ g ∈ Γ') → (∀ g, g ∈ P ↔ Φ g ∈ P') →
    (AllRep K' fun ρ => HasWall Γ' K' P' P' c η η (fun g => N * η g) ρ) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k))) →
      ∃ (A : ℂ → ℂ) (H : ℂ → G → ℂ) (R : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧ (∀ g, Differentiable ℂ (H · g)) ∧
        Continuous (fun y : ℂ × G => H y.1 y.2) ∧
        (∀ z : ℂ, R < z.re → ∀ g, H z g = A z * GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) ∧
        ∀ a b : ℝ, R < a → b < -R → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g,
          ‖H z g‖ ≤ M * (‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (a * η (Φ x)) : ℂ)) g‖ +
            ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp ((N - b) * η (Φ x)) : ℂ)) g‖)

def TScal : Prop := SecLaw → WallLaw → Scal

def Div : Prop :=
  ∀ (D : D7) (T : HSp D) (e H : ℂ → GA D T → ℂ) (A : ℂ → ℂ) (R : ℝ), Differentiable ℂ A → (∃ z, A z ≠ 0) →
    (∀ g, Differentiable ℂ (H · g)) → Continuous (fun y : ℂ × GA D T => H y.1 y.2) →
    (∀ z : ℂ, R < z.re → ∀ g, H z g = A z * e z g) →
    (∀ r : ℝ, ∃ (C : ℝ) (N : ℕ), ∀ z : ℂ, ‖z‖ ≤ r → ∀ g, ‖H z g‖ ≤ C * GlobalTheory.Grow.height T g ^ N) → GlobalTheory.EisCont.ContMod T e

def TTop : Prop := CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll → Chart → Scal → Div →
  GlobalTheory.Published.SiegelEisensteinContinuation

end ResidueKilled.Tr

end
