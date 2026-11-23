import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ComplexConjugate

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E n) in

def infAt (w : InfinitePlace E) : GA E n →* PositivityTheory.RgTw.G n :=
  Matrix.GeneralLinearGroup.map ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).comp (pInf E))

variable (E n) in

def finOf : GA E n →* GL (Fin n) (Af E) := Matrix.GeneralLinearGroup.map (pFin E)

variable (E n) in

def thetaF (g : GL (Fin n) (Af E)) : GL (Fin n) (Af E) := finOf E n (thetaA E n (finGL E n g))

def IsHeckeF (K : Subgroup (GL (Fin n) (Af E))) (h : GL (Fin n) (Af E) → ℂ) : Prop :=
  HasCompactSupport h ∧ ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, h (k₁ * g * k₂) = h g

def heckeOp [MeasurableSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))) (h : GL (Fin n) (Af E) → ℂ)
    (φ : GA E n → ℂ) : GA E n → ℂ :=
  fun x => ∫ g, h g * φ (x * finGL E n g) ∂μf

def phiProd (lam : InfinitePlace E → Fin n → ℤ)
    (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
    (h : GL (Fin n) (Af E) → ℂ) (y : H E n 0) : ℂ :=
  (∏ w, PositivityTheory.RgBcC.phiOf (PositivityTheory.RgBcC.lefE n (lam w)) (PositivityTheory.RgBcC.lefT n (lam w)) (k w) (infAt E n w y.1)) *
    h (finOf E n y.1)

def ThetaFixedGlobalCharacter : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
    ThetaFix π → ∀ lam : InfinitePlace E → Fin n → ℤ, (∀ w, Antitone (lam w)) →
    (∀ w, HasInfCharGL π.V w.embedding (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding)
        (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) false) Finset.univ.val)) →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ) →
    ∀ [MeasurableSpace (PositivityTheory.RgTw.G n)] [BorelSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
      [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (μ : Measure (H E n 0)) [μ.IsHaarMeasure],
    ∃ (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y) (c : ℂ),
      Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ y ∈ Y, ∀ k ∈ K, finRep E n k y = y) ∧
      (∀ h, IsHeckeF K h → ∀ y : Y, (((ρ h y : Y) : Sm E n) : GA E n → ℂ) = heckeOp μf h ((y : Sm E n) : GA E n → ℂ)) ∧
      (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      A * A = 1 ∧ (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ c ≠ 0 ∧
      ∀ (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lam w)) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μ π (phiProd lam k h) (c * (∏ w, val w (PositivityTheory.RgBcC.infOf (lam w))) * LinearMap.trace ℂ Y (ρ h * A))

end PositivityTheory.Rg.BcB.Desc

end
