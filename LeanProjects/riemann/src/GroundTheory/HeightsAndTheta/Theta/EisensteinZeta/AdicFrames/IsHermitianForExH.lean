import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.CompactFormulaUnitary
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.HeightsAndTheta.Theta.GaussianExample

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

open MeasureTheory Topology Filter Matrix TensorProduct NumberField IsDedekindDomain
  GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal NNReal NumberField.AdeleRing

noncomputable section

section Frames

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {p : ℕ}

def IsFree (X : Matrix ι (Fin p) A) : Prop :=
  ∃ Y : Matrix (Fin p) ι A, Y * X = 1

end Frames

section Local

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ℕ)

abbrev scTop : TopologicalSpace (R ⊗[K] E) := moduleTopology R (R ⊗[K] E)

def FrameSp : Type _ := Matrix ι (Fin p) (R ⊗[K] E)

instance : AddCommGroup (FrameSp K E R ι p) :=
  inferInstanceAs (AddCommGroup (Matrix ι (Fin p) (R ⊗[K] E)))

instance : TopologicalSpace (FrameSp K E R ι p) :=
  @Pi.topologicalSpace ι _ fun _ ↦ @Pi.topologicalSpace (Fin p) _ fun _ ↦ scTop K E R

instance : MeasurableSpace (FrameSp K E R ι p) := borel _

instance : BorelSpace (FrameSp K E R ι p) := ⟨rfl⟩

def hermSub : AddSubgroup (Matrix (Fin p) (Fin p) (R ⊗[K] E)) where
  carrier := {S | (S.map (conjBase K E R))ᵀ = S}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def HermSp : Type _ := ↥(hermSub K E R p)

instance : AddCommGroup (HermSp K E R p) := inferInstanceAs (AddCommGroup ↥(hermSub K E R p))

instance : TopologicalSpace (HermSp K E R p) :=
  TopologicalSpace.induced (fun S : ↥(hermSub K E R p) ↦ (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)))
    (@Pi.topologicalSpace (Fin p) _ fun _ ↦ @Pi.topologicalSpace (Fin p) _ fun _ ↦ scTop K E R)

instance : MeasurableSpace (HermSp K E R p) := borel _

instance : BorelSpace (HermSp K E R p) := ⟨rfl⟩

variable {K E R ι p}

def HermSp.mat (S : HermSp K E R p) : Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  (show ↥(hermSub K E R p) from S).1

variable (K E R) in

def framePair (H : Matrix ι ι E) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (X' : Matrix ι (Fin q) (R ⊗[K] E)) : Matrix (Fin p) (Fin q) (R ⊗[K] E) :=
  (X.map (conjBase K E R))ᵀ *
    H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E) * X'

variable (K E R) in

def gram (H : Matrix ι ι E) (X : Matrix ι (Fin p) (R ⊗[K] E)) :
    Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  framePair K E R H X X

variable (K E R) in

def trR : R ⊗[K] E →ₗ[R] R := Algebra.trace R (R ⊗[K] E)

def framePairing (ψ : AddChar R Circle) (H : Matrix ι ι E) :
    FrameSp K E R ι p → FrameSp K E R ι p → Circle :=
  fun X X' ↦ ψ (trR K E R (Matrix.trace (framePair K E R H (show Matrix ι (Fin p) _ from X)
    (show Matrix ι (Fin p) _ from X'))))

def hermPairing (ψ : AddChar R Circle) : HermSp K E R p → HermSp K E R p → Circle :=
  fun S S' ↦ ψ ((2 : K)⁻¹ • trR K E R (Matrix.trace (S.mat * S'.mat)))

def fourierT {V : Type*} [MeasurableSpace V] (χ : V → V → Circle) (μ : Measure V) (f : V → ℂ)
    (y : V) : ℂ :=
  ∫ x, (χ x y : ℂ) * f x ∂μ

def IsSelfDual {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → Circle) (μ : Measure V) : Prop :=
  μ.IsAddHaarMeasure ∧
    ∀ f : V → ℂ, Continuous f → Integrable f μ → Integrable (fourierT χ μ f) μ →
      ∫ y, fourierT χ μ f y ∂μ = f 0

def gramPre (H : Matrix ι ι E) (U : Set (HermSp K E R p)) : Set (FrameSp K E R ι p) :=
  {X | ∃ S ∈ U, S.mat = gram K E R H (show Matrix ι (Fin p) _ from X)}

def freeSet : Set (FrameSp K E R ι p) := {X | IsFree (show Matrix ι (Fin p) (R ⊗[K] E) from X)}

def isoSet (H : Matrix ι ι E) : Set (FrameSp K E R ι p) :=
  {X | IsFree (show Matrix ι (Fin p) (R ⊗[K] E) from X) ∧ gram K E R H X = 0}

def IsIsoFibre (H : Matrix ι ι E) (dX : Measure (FrameSp K E R ι p))
    (dS : Measure (HermSp K E R p)) (μ : Measure (FrameSp K E R ι p)) : Prop :=
  μ (isoSet H)ᶜ = 0 ∧
    (∀ C : Set (FrameSp K E R ι p), IsCompact C → C ⊆ freeSet → μ C < ⊤) ∧
    ∀ φ : FrameSp K E R ι p → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeSet →
      Tendsto (fun U : Set (HermSp K E R p) ↦ (dS U).toReal⁻¹ * ∫ X in gramPre H U, φ X ∂dX)
        ((𝓝 (0 : HermSp K E R p)).smallSets ⊓ 𝓟 {U | IsOpen U ∧ (0 : HermSp K E R p) ∈ U})
        (𝓝 (∫ X, φ X ∂μ))

end Local

section Adelic

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

variable (K) in

def infProj : 𝔸[K] →ₐ[K] InfiniteAdeleRing K :=
  (AlgHom.fst K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (adeleRingEquivProd K).toAlgHom

def psiInf (ψ : AddChar 𝔸[K] Circle) : AddChar (InfiniteAdeleRing K) Circle :=
  ψ.compAddMonoidHom GroundTheory.Global.infiniteAdeleInl

def psiAt (ψ : AddChar 𝔸[K] Circle) (v : HeightOneSpectrum (𝓞 K)) :
    AddChar (v.adicCompletion K) Circle :=
  ψ.compAddMonoidHom (GroundTheory.Global.finitePlaceIncl v)

variable (K) in

def ratIso (H : Matrix ι ι E) (p : ℕ) : Set (Matrix ι (Fin p) E) :=
  {X | (X.map (conjHom K E))ᵀ * H * X = 0 ∧ IsFree X}

variable (K) in

def toAdelic (X : Matrix ι (Fin p) E) : Matrix ι (Fin p) (𝔸[K] ⊗[K] E) :=
  X.map (Algebra.TensorProduct.includeRight : E →ₐ[K] 𝔸[K] ⊗[K] E)

def act {R : Type*} [CommRing R] [Algebra K R] {H : Matrix ι ι E} (g : unitaryPoints K E H R)
    (X : Matrix ι (Fin p) (R ⊗[K] E)) : Matrix ι (Fin p) (R ⊗[K] E) :=
  ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) * X

def compInf (X : Matrix ι (Fin p) (𝔸[K] ⊗[K] E)) : FrameSp K E (InfiniteAdeleRing K) ι p :=
  X.map (tensorMap E (infProj K))

def compAt (v : HeightOneSpectrum (𝓞 K)) (X : Matrix ι (Fin p) (𝔸[K] ⊗[K] E)) :
    FrameSp K E (v.adicCompletion K) ι p :=
  X.map (tensorMap E (adeleFiniteEval K v))

variable (K E ι p) in

def latticeFrames (v : HeightOneSpectrum (𝓞 K)) : Set (FrameSp K E (v.adicCompletion K) ι p) :=
  {X | ∀ j, (fun i ↦ (show Matrix ι (Fin p) _ from X) i j) ∈
    stdLattice ι (v.adicCompletion K) (Module.finBasis K E)
      (v.adicCompletionIntegers K).toSubring}

def sizeInf (X : FrameSp K E (InfiniteAdeleRing K) ι p) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ w : InfinitePlace K,
    ‖infiniteAdeleRingEquivPi K
      ((Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Module.finBasis K E)).repr
        ((show Matrix ι (Fin p) _ from X) i j) k) w‖

def IsRapidDecay (Φ : FrameSp K E (InfiniteAdeleRing K) ι p → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ X, (1 + sizeInf X) ^ N * ‖Φ X‖ ≤ C

def pureC (Φinf : FrameSp K E (InfiniteAdeleRing K) ι p → ℂ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), FrameSp K E (v.adicCompletion K) ι p → ℂ)
    (X : Matrix ι (Fin p) (𝔸[K] ⊗[K] E)) : ℂ :=
  Φinf (compInf X) * ∏ᶠ v, Φ v (compAt v X)

def pureE (Φinf : FrameSp K E (InfiniteAdeleRing K) ι p → ℝ≥0∞)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), FrameSp K E (v.adicCompletion K) ι p → ℝ≥0∞)
    (X : Matrix ι (Fin p) (𝔸[K] ⊗[K] E)) : ℝ≥0∞ :=
  Φinf (compInf X) * ∏ᶠ v, Φ v (compAt v X)

variable (K) in

abbrev ratPts (H : Matrix ι ι E) : Subgroup (unitaryPoints K E H 𝔸[K]) :=
  (unitaryDiagonal K H).range

instance (H : Matrix ι ι E) : DiscreteTopology (ratPts K H) :=
  discreteTopology_unitaryDiagonal_range (K := K) H

variable (K) in

def thetaSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (H : Matrix ι ι E) (p : ℕ)
    (Φ : Matrix ι (Fin p) (𝔸[K] ⊗[K] E) → M) (h : unitaryPoints K E H 𝔸[K]) : M :=
  ∑' X : ratIso K H p, Φ (act h⁻¹ (toAdelic K (X : Matrix ι (Fin p) E)))

variable (K) in

def thetaSumQ {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (H : Matrix ι ι E) (p : ℕ)
    (Φ : Matrix ι (Fin p) (𝔸[K] ⊗[K] E) → M) (x : RightCosetSpace (ratPts K H)) : M :=
  thetaSum K H p Φ x.out

end Adelic

section FibreOf

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

def IsIsoFibreOf (ψR : AddChar R Circle) (H : Matrix ι ι E) (μ : Measure (FrameSp K E R ι p)) :
    Prop :=
  ∃ (dX : Measure (FrameSp K E R ι p)) (dS : Measure (HermSp K E R p)),
    IsSelfDual (framePairing ψR H) dX ∧ IsSelfDual (hermPairing ψR) dS ∧ IsIsoFibre H dX dS μ

end FibreOf

def SelfDual.ExistsUnique.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [IsTotallyReal K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E),
    IsHermitianFor (conjHom K E) H → IsUnit H.det →
    ∀ (p : ℕ) (ψ : AddChar 𝔸[K] Circle), Continuous ψ → ψ ≠ 1 →
    (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) →
    (∃! dX : Measure (FrameSp K E (InfiniteAdeleRing K) ι p),
        IsSelfDual (framePairing (psiInf ψ) H) dX) ∧
      (∃! dS : Measure (HermSp K E (InfiniteAdeleRing K) p),
        IsSelfDual (hermPairing (psiInf ψ)) dS) ∧
      ∀ v : HeightOneSpectrum (𝓞 K),
        (∃! dX : Measure (FrameSp K E (v.adicCompletion K) ι p),
          IsSelfDual (framePairing (psiAt ψ v) H) dX) ∧
        (∃! dS : Measure (HermSp K E (v.adicCompletion K) p),
          IsSelfDual (hermPairing (psiAt ψ v)) dS)

def IsoFibre.ExistsUnique.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [IsTotallyReal K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E),
    IsHermitianFor (conjHom K E) H → IsUnit H.det →
    ∀ (p : ℕ) (ψ : AddChar 𝔸[K] Circle), Continuous ψ → ψ ≠ 1 →
    (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) →
    (∃! μ : Measure (FrameSp K E (InfiniteAdeleRing K) ι p), IsIsoFibreOf (psiInf ψ) H μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 K),
        ∃! μ : Measure (FrameSp K E (v.adicCompletion K) ι p), IsIsoFibreOf (psiAt ψ v) H μ

def SiegelIsotropic.StatementFrom (d : ℕ) : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [IsTotallyReal K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E) [Fact (IsUnit H.det)],
    IsHermitianFor (conjHom K E) H →
    ∀ p : ℕ, 1 ≤ p → 2 * p + d ≤ Fintype.card ι →
    ∀ ψ : AddChar 𝔸[K] Circle, Continuous ψ → ψ ≠ 1 → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) →
    ∀ (μinf : Measure (FrameSp K E (InfiniteAdeleRing K) ι p))
      (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (FrameSp K E (v.adicCompletion K) ι p)),
    IsIsoFibreOf (psiInf ψ) H μinf → (∀ v, IsIsoFibreOf (psiAt ψ v) H (μ v)) →
    ∀ dh : Measure (unitaryPoints K E H 𝔸[K]), dh.IsHaarMeasure →
    quotientMeasure (ratPts K H) dh Set.univ = 1 →
    ∀ Φinf : FrameSp K E (InfiniteAdeleRing K) ι p → ℂ, Continuous Φinf → IsRapidDecay Φinf →
    ∀ Φ : ∀ v : HeightOneSpectrum (𝓞 K), FrameSp K E (v.adicCompletion K) ι p → ℂ,
    (∀ v, IsLocallyConstant (Φ v) ∧ HasCompactSupport (Φ v)) →
    {v | Φ v ≠ (latticeFrames K E ι p v).indicator 1}.Finite →
    ∫⁻ x, thetaSumQ K H p (fun X ↦ (‖pureC Φinf Φ X‖₊ : ℝ≥0∞)) x
        ∂quotientMeasure (ratPts K H) dh < ⊤ ∧
      Integrable Φinf μinf ∧ (∀ v, Integrable (Φ v) (μ v)) ∧
      Summable (fun v ↦ ‖(∫ X, Φ v X ∂μ v) - 1‖) ∧
      ∫ x, thetaSumQ K H p (pureC Φinf Φ) x ∂quotientMeasure (ratPts K H) dh =
        (∫ X, Φinf X ∂μinf) * ∏' v, ∫ X, Φ v X ∂μ v

def SiegelIsotropic.BorelFrom (d : ℕ) : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [IsTotallyReal K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E) [Fact (IsUnit H.det)],
    IsHermitianFor (conjHom K E) H →
    ∀ p : ℕ, 1 ≤ p → 2 * p + d ≤ Fintype.card ι →
    ∀ ψ : AddChar 𝔸[K] Circle, Continuous ψ → ψ ≠ 1 → (∀ k : K, ψ (algebraMap K 𝔸[K] k) = 1) →
    ∀ (μinf : Measure (FrameSp K E (InfiniteAdeleRing K) ι p))
      (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (FrameSp K E (v.adicCompletion K) ι p)),
    IsIsoFibreOf (psiInf ψ) H μinf → (∀ v, IsIsoFibreOf (psiAt ψ v) H (μ v)) →
    ∀ dh : Measure (unitaryPoints K E H 𝔸[K]), dh.IsHaarMeasure →
    quotientMeasure (ratPts K H) dh Set.univ = 1 →
    ∀ Φinf : FrameSp K E (InfiniteAdeleRing K) ι p → ℝ≥0∞, Measurable Φinf →
    ∀ Φ : ∀ v : HeightOneSpectrum (𝓞 K), FrameSp K E (v.adicCompletion K) ι p → ℝ≥0∞,
    (∀ v, Measurable (Φ v)) →
    {v | Φ v ≠ (latticeFrames K E ι p v).indicator 1}.Finite →
    Multipliable (fun v ↦ ∫⁻ X, Φ v X ∂μ v) ∧
      ∫⁻ x, thetaSumQ K H p (pureE Φinf Φ) x ∂quotientMeasure (ratPts K H) dh =
        (∫⁻ X, Φinf X ∂μinf) * ∏' v, ∫⁻ X, Φ v X ∂μ v

def SiegelIsotropic.Statement : Prop := SiegelIsotropic.StatementFrom 1

def SiegelIsotropic.Borel.Statement : Prop := SiegelIsotropic.BorelFrom 1

def SiegelIsotropic.Range2.Statement : Prop := SiegelIsotropic.StatementFrom 2

def SiegelIsotropic.Range2.Borel.Statement : Prop := SiegelIsotropic.BorelFrom 2

section Example

def exH : Matrix (Fin 3) (Fin 3) GaussQ := Matrix.diagonal ![1, -1, 1]

def exX : Matrix (Fin 3) (Fin 1) GaussQ := Matrix.of fun i _ ↦ ![1, 1, 0] i

theorem isHermitianFor_exH : IsHermitianFor (conjHom ℚ GaussQ) exH := by
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [exH, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.map_apply]

theorem isUnit_det_exH : IsUnit exH.det := by
  rw [exH, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem exX_mem_ratIso : exX ∈ ratIso ℚ exH 1 := by
  refine ⟨?_, Matrix.of fun _ j ↦ ![1, 0, 0] j, ?_⟩
  · refine Matrix.ext fun i j ↦ ?_
    fin_cases i
    fin_cases j
    simp [exX, exH, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  · refine Matrix.ext fun i j ↦ ?_
    fin_cases i
    fin_cases j
    simp [exX, Matrix.mul_apply, Fin.sum_univ_three]

end Example

end

end IsoFrames

end GroundTheory.Heights₂.Theta
