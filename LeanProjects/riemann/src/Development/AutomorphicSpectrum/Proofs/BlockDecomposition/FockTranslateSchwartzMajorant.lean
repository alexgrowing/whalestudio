import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {ρ r s p : ℕ}

def rowT (y : Mx D (r + s) p) : Mx D r p := fun i j => y (Fin.castAdd s i) j

def rowB (y : Mx D (r + s) p) : Mx D s p := fun i j => y (Fin.natAdd r i) j

def rowJ (x : Mx D r p) (z : Mx D s p) : Mx D (r + s) p :=
  fun i j => Fin.addCases (motive := fun _ => AE D) (fun a => x a j) (fun b => z b j) i

def IsBlockSL2Embedding (b : HermE D (r + s)) (b₁ : HermE D r) (b₂ : HermE D s) : Prop :=
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.castAdd s j) = b₁.1 i j) ∧
  (∀ i j, b.1 (Fin.natAdd r i) (Fin.natAdd r j) = b₂.1 i j) ∧
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.natAdd r j) = 0) ∧ ∀ i j, b.1 (Fin.natAdd r j) (Fin.castAdd s i) = 0

def Total (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (b₀ : HermE D ρ) (μ : Measure (Mx D ρ p)) : Prop :=
  ∀ u : Mx D ρ p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
    (∀ Ω, IsTh ψ χ θ b₀ μ Ω → ∫ y, u y * conj (Ω 1 y) ∂μ = 0) → u = 0

abbrev V1 (D : D7) : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1

def WeilCont : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n,
      Continuous fun u : G D n × Mx D V.rank n => (ω u.1 Φ).1 u.2

def WeilKFin : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s →
      ∃ W : Submodule ℂ (Mx D V.rank n → ℂ), FiniteDimensional ℂ W ∧ W ≤ fockA θ V n l s ∧ ∀ k ∈ K D n, (ω k Φ).1 ∈ W

def OrbitMaj : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ f ∈ fockA θ (V1 D) n l (fun _ => 1), ∀ A₁ A₂ : Set (Mx D n n), IsCompact A₁ → IsCompact A₂ →
      ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
        ∀ a : GL (Fin n) (AE D), a.1 ∈ A₁ → (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
          ‖f (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ‖M y‖

def IwaCpt : Prop :=
  ∀ (D : D7) (n : ℕ) (C : Set (G D n)), IsCompact C → ∃ (A₁ A₂ : Set (Mx D n n)) (R : ℝ), IsCompact A₁ ∧ IsCompact A₂ ∧
    ∀ h ∈ C, ∃ (m t k : G D n) (a : GL (Fin n) (AE D)) (b : Mx D n n), k ∈ K D n ∧ h = m * t * k ∧
      mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat t = blk4 1 b 0 1 ∧ a.1 ∈ A₁ ∧ (a⁻¹).1 ∈ A₂ ∧
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≤ R

def FockTranslateSchwartzMajorant : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ 1 → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D (V1 D).rank n)) (𝓕 : Set (Mx D (V1 D).rank n)), IsCovolOne (ratMx D (V1 D).rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ (V1 D).rank n), IsWeilSch ψ χ θ (V1 D) μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → (∀ τ, l τ ≠ 0) → ∀ Φ : schwartzA θ (V1 D).rank n,
      Φ.1 ∈ fockA θ (V1 D) n l (fun _ => 1) → ∀ C : Set (G D n), IsCompact C →
      ∃ M ∈ schwartzA θ (V1 D).rank n, ∀ h ∈ C, ∀ y, ‖(ω h Φ).1 y‖ ≤ ‖M y‖

def SchwTensor : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r s p : ℕ, ∀ φ ∈ schwartzA θ r p, ∀ φ' ∈ schwartzA θ s p,
    (fun y : Mx D (r + s) p => φ (rowT y) * φ' (rowB y)) ∈ schwartzA θ (r + s) p

def ProdTh : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → ∀ ψ, IsCharAF D.host.F ψ →
    ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)),
    IsBlockSL2Embedding b br bs → ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      IsTh ψ (χr * χs) θ b ((μr.prod μs).map fun z => rowJ z.1 z.2) fun h y => Ωr h (rowT y) * Ωs h (rowB y)

def ProdMeas : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    μ = (μr.prod μs).map fun z => rowJ z.1 z.2

def EucTotal : Prop :=
  ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    (lam : Measure Z) [lam.IsAddHaarMeasure] (ι : Type) [Fintype ι] (c : ι → Z →L[ℝ] ℂ), (∀ z, (∀ k, c k z = 0) → z = 0) →
    ∀ A : Subalgebra ℂ (Z → ℂ), (∀ k, (fun z => c k z) ∈ A) → (∀ k, (fun z => conj (c k z)) ∈ A) →
    ∀ (g : Z → ℝ), Continuous g → (∀ z, 0 < g z) → ∀ C a : ℝ, 0 < a → (∀ z, g z ≤ C * Real.exp (-a * ‖z‖ ^ 2)) →
    ∀ w : Z → ℂ, Continuous w → (∃ B : ℝ, ∀ z, ‖w z‖ ≤ B) → (∀ P ∈ A, ∫ z, w z * P z * (g z : ℂ) ∂lam = 0) → w = 0

def FockTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ (μ : Measure (Mx D (V1 D).rank p)) (𝓕 : Set (Mx D (V1 D).rank p)), IsCovolOne (ratMx D (V1 D).rank p) μ 𝓕 →
    ∀ u : Mx D (V1 D).rank p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
      (∀ φ ∈ fockA θ (V1 D) p l (fun _ => 1), ∫ y, u y * conj (φ y) ∂μ = 0) → u = 0

def OneTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 1 p)) (𝓕 : Set (Mx D 1 p)), IsCovolOne (ratMx D 1 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 1, b₀.1.det ≠ 0 → ∀ χ, IsHeckeChar D χ → ResEta D χ 1 →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ

def ZeroTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 0 p)) (𝓕 : Set (Mx D 0 p)), IsCovolOne (ratMx D 0 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 0, ∀ θ, IsInfFam θ → Total ψ 1 θ b₀ μ

def StepTotal : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ →
    ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)), IsBlockSL2Embedding b br bs →
      Total ψ χr θ br μr → Total ψ χs θ bs μs → Total ψ (χr * χs) θ b μ

end GlobalTheory.CompanionTheory.ThTot

end
