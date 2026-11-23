import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace SwmCone

open MeasureTheory Topology Filter Matrix TensorProduct NumberField IsDedekindDomain
  GroundTheory.Automorphic GroundTheory.Heights₂.Theta.IsoFrames
open scoped ENNReal NNReal

attribute [local instance] IsoFrames.scTop

section Local

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (K E R) in

def cTr {m l : Type*} (g : Matrix m l (R ⊗[K] E)) : Matrix l m (R ⊗[K] E) :=
  (g.map (conjBase K E R))ᵀ

def frameMul (X : FrameSp K E R ι n) (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from (show Matrix ι (Fin n) (R ⊗[K] E) from X) * g

def frameSMul (h : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) : FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from h * (show Matrix ι (Fin n) (R ⊗[K] E) from X)

variable (K E R ι) in

def gramFibre (Q : Matrix ι ι E) (T : HermSp K E R n) : Set (FrameSp K E R ι n) :=
  {X | IsoFrames.gram K E R Q (show Matrix ι (Fin n) (R ⊗[K] E) from X) = T.mat}

variable (R) in

def modE [IsTopologicalRing R] [LocallyCompactSpace R] (z : (R ⊗[K] E)ˣ) : ℝ≥0 :=
  distribHaarChar R (Units.map (Algebra.norm R : R ⊗[K] E →* R) z)

def IsGramDensity (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (φ : FrameSp K E R ι n → ℂ) (Om : Set (HermSp K E R n))
    (δ : HermSp K E R n → ℂ) : Prop :=
  IsOpen Om ∧ ContinuousOn δ Om ∧
    ∀ f : Matrix (Fin n) (Fin n) (R ⊗[K] E) → ℂ, Continuous f → HasCompactSupport f →
      tsupport (fun S : HermSp K E R n ↦ f S.mat) ⊆ Om →
      ∫ X, f (IsoFrames.gram K E R Q (show Matrix ι (Fin n) (R ⊗[K] E) from X)) * φ X ∂dX =
        ∫ S, f S.mat * δ S ∂dS

def IsFibreMeasure (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (T : HermSp K E R n) (μ : Measure (FrameSp K E R ι n)) :
    Prop :=
  IsFiniteMeasureOnCompacts μ ∧ μ (gramFibre K E R ι Q T)ᶜ = 0 ∧
    (∀ h : unitaryPoints K E Q R,
      μ.map (frameSMul ((h : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))) = μ) ∧
    ∀ φ : FrameSp K E R ι n → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ (Om : Set (HermSp K E R n)) (δ : HermSp K E R n → ℂ),
        T ∈ Om ∧ IsGramDensity Q dX dS φ Om δ ∧ δ T = ∫ X, φ X ∂μ

variable [IsTopologicalRing R] [LocallyCompactSpace R]

def ConeChart (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) (T : HermSp K E R n) (B : Set (GL (Fin n) (R ⊗[K] E)))
    (μ : Measure (FrameSp K E R ι n)) : Prop :=
  ∃ (Om : Set (HermSp K E R n)) (e : B ≃ₜ Om), IsOpen Om ∧ T ∈ Om ∧
    (∀ g : B, (e g : HermSp K E R n).mat =
      cTr K E R ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * T.mat *
        ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∧
    (∃ e₂ : (gramFibre K E R ι Q T) × B ≃ₜ (gramPre Q Om : Set (FrameSp K E R ι n)),
      ∀ p, (e₂ p : FrameSp K E R ι n) = frameMul (p.1 : FrameSp K E R ι n)
        ((p.2 : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∧
    ∀ φ : FrameSp K E R ι n → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ δ : HermSp K E R n → ℂ, IsGramDensity Q dX dS φ Om δ ∧
        ∀ g : B, δ (e g) =
          (((modE R (Matrix.GeneralLinearGroup.det (g : GL (Fin n) (R ⊗[K] E))) : ℝ) ^
              ((Fintype.card ι : ℤ) - n) : ℝ) : ℂ) *
            ∫ X, φ (frameMul X ((g : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))) ∂μ

def GeneralTAt (Q : Matrix ι ι E) (dX : Measure (FrameSp K E R ι n))
    (dS : Measure (HermSp K E R n)) : Prop :=
  ∀ T : HermSp K E R n, IsUnit T.mat.det →
    (∃ μ, IsFibreMeasure Q dX dS T μ) ∧
    ∀ (g₀ : GL (Fin n) (R ⊗[K] E)) (T' : HermSp K E R n),
      T'.mat = cTr K E R (g₀ : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * T.mat * g₀ →
      ∀ μ μ' : Measure (FrameSp K E R ι n), IsFibreMeasure Q dX dS T μ →
        IsFibreMeasure Q dX dS T' μ' →
        μ' = ((modE R (Matrix.GeneralLinearGroup.det g₀)) ^ ((Fintype.card ι : ℤ) - n) : ℝ≥0) •
          μ.map (fun X ↦ frameMul X (g₀ : Matrix (Fin n) (Fin n) (R ⊗[K] E)))

end Local

section Groups

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

variable (E) in

def realConeGroup (w : InfinitePlace K) (hw : w.IsReal) (n : ℕ) :
    Set (GL (Fin n) (w.Completion ⊗[K] E)) :=
  {g | (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) (w.Completion ⊗[K] E)) i j = 0) ∧
    ∀ i, ∃ u : w.Completion, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u ∧
      (g : Matrix (Fin n) (Fin n) (w.Completion ⊗[K] E)) i i = algebraMap _ _ u}

variable (E) in

def finiteConeGroup (v : HeightOneSpectrum (𝓞 K)) (k n : ℕ) :
    Set (GL (Fin n) (v.adicCompletion K ⊗[K] E)) :=
  {g | (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j = 0) ∧
    (∀ i, ∃ u : v.adicCompletion K, ‖u - 1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k ∧
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i i = algebraMap _ _ u) ∧
    ∀ i j, i < j →
      ‖Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] E)
          ((g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j)‖ ≤
          ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k ∧
        ‖Algebra.norm (v.adicCompletion K)
          ((g : Matrix (Fin n) (Fin n) (v.adicCompletion K ⊗[K] E)) i j)‖ ≤
          ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ (2 * k)}

end Groups

section Statements

def ConeReal.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (w : InfinitePlace K) (hw : w.IsReal)
    (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    ∀ (dX : Measure (FrameSp K E w.Completion ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E w.Completion n)) [dS.IsAddHaarMeasure]
      (T : HermSp K E w.Completion n) (t : Fin n → w.Completion), (∀ i, t i ≠ 0) →
      T.mat = Matrix.diagonal (fun i ↦ algebraMap w.Completion (w.Completion ⊗[K] E) (t i)) →
      ∃ μ : Measure (FrameSp K E w.Completion ι n),
        IsFibreMeasure Q dX dS T μ ∧ ConeChart Q dX dS T (realConeGroup E w hw n) μ

def ConeFinite.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (v : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    ∀ (dX : Measure (FrameSp K E (v.adicCompletion K) ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E (v.adicCompletion K) n)) [dS.IsAddHaarMeasure]
      (T : HermSp K E (v.adicCompletion K) n) (t : Fin n → v.adicCompletion K), (∀ i, t i ≠ 0) →
      T.mat = Matrix.diagonal
        (fun i ↦ algebraMap (v.adicCompletion K) (v.adicCompletion K ⊗[K] E) (t i)) →
      ∃ μ : Measure (FrameSp K E (v.adicCompletion K) ι n),
        IsFibreMeasure Q dX dS T μ ∧
        ∀ k : ℕ, ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ k < ‖(2 : v.adicCompletion K)‖ →
          ConeChart Q dX dS T (finiteConeGroup E v k n) μ

def ConeGeneral.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (Q : Matrix ι ι E),
    GroundTheory.Automorphic.IsHermitianFor (GroundTheory.Automorphic.conjHom K E) Q → IsUnit Q.det →
    (∀ (w : InfinitePlace K), w.IsReal →
      ∀ (dX : Measure (FrameSp K E w.Completion ι n)) [dX.IsAddHaarMeasure]
        (dS : Measure (HermSp K E w.Completion n)) [dS.IsAddHaarMeasure],
        GeneralTAt Q dX dS) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (dX : Measure (FrameSp K E (v.adicCompletion K) ι n)) [dX.IsAddHaarMeasure]
      (dS : Measure (HermSp K E (v.adicCompletion K) n)) [dS.IsAddHaarMeasure],
      GeneralTAt Q dX dS

end Statements

section Ties

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]

variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]

def hermOne (n : ℕ) : HermSp K E R n :=
  ⟨1, by
    show ((1 : Matrix (Fin n) (Fin n) (R ⊗[K] E)).map (conjBase K E R))ᵀ = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]⟩

end Ties

end SwmCone

end GroundTheory.Heights₂.Theta
