import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlagBundles

open MeasureTheory Metric Set
open scoped ComplexConjugate Matrix ENNReal

noncomputable section

def logKernel (s : ℝ) : ℝ := (1 / 2) * Real.log ((1 - s) / 2)

def gKernel (R : Type*) [CommRing R] (k : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ j ∈ Finset.range k,
    (MvPolynomial.X 0 ^ (2 * j + 1) * MvPolynomial.X 1 ^ (2 * k - 1 - 2 * j) -
      MvPolynomial.X 0 ^ (2 * j) * MvPolynomial.X 1 ^ (2 * k - 2 * j))

def gKernelEval {R : Type*} [CommRing R] (k : ℕ) (x y : R) : R :=
  MvPolynomial.eval ![x, y] (gKernel R k)

def gMixed (R : Type*) [CommRing R] (k : ℕ) : MvPolynomial (Fin 2) R :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (gKernel R k))

def unipotentMatrix {R : Type*} [CommRing R] {N : ℕ} (a : Fin N → Fin N → R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun l m => if l = m then 1 else if l < m then a m l else 0

def minorColumns {N : ℕ} (l m : Fin N) : Fin (l.val + 1) → Fin N :=
  fun j => if h : j.val < l.val then ⟨j.val, lt_trans h l.isLt⟩ else m

def pluckerCoord {R : Type*} [CommRing R] {l N : ℕ} (V : Matrix (Fin l) (Fin N) R)
    (I : Finset (Fin N)) : R :=
  if h : I.card = l then (V.submatrix id (I.orderEmbOfFin h)).det else 0

def squareMinor {R : Type*} [CommRing R] {N : ℕ} (l : ℕ) (g : Matrix (Fin N) (Fin N) R)
    (J I : Finset (Fin N)) : R :=
  if h : J.card = l ∧ I.card = l then
    (g.submatrix (J.orderEmbOfFin h.1) (I.orderEmbOfFin h.2)).det else 0

abbrev LowerPairs (N : ℕ) := {q : Fin N × Fin N // q.2 < q.1}

abbrev omitStepAlgebra (R : Type*) [CommRing R] {A : Type*} (p : A) :
    Algebra (MvPolynomial {q // q ≠ p} R) (MvPolynomial A R) :=
  (MvPolynomial.rename (R := R) (Subtype.val : {q // q ≠ p} → A)).toRingHom.toAlgebra

def gramWedgeNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (e f : E) : ℝ :=
  Real.sqrt (‖e‖ ^ 2 * ‖f‖ ^ 2 - ‖inner ℂ e f‖ ^ 2)

def eps₁ (R : Type*) [CommRing R] : Fin 2 → R := Pi.single 0 1

def eps₂ (R : Type*) [CommRing R] : Fin 2 → R := Pi.single 1 1

def lineA {R : Type*} [CommRing R] (a : R) : Submodule R (Fin 2 → R) :=
  Submodule.span R {eps₁ R + a • eps₂ R}

def lineB {R : Type*} [CommRing R] (b : R) : Submodule R (Fin 2 → R) :=
  Submodule.span R {b • eps₁ R + eps₂ R}

abbrev diagQuot (R : Type*) [CommRing R] :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) R)}

abbrev crossQuot (R : Type*) [CommRing R] :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span {(1 - MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) R)}

abbrev diagIdeal (R : Type*) [CommRing R] : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {MvPolynomial.X 0 - MvPolynomial.X 1}

abbrev crossIdeal (R : Type*) [CommRing R] : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {1 - MvPolynomial.X 0 * MvPolynomial.X 1}

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

def blochVector (e : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => (inner ℂ e (WithLp.toLp 2 (pauli i *ᵥ WithLp.ofLp e))).re

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 := Metric.sphere (0 : E3) 1

def sphereProb : Measure S2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

def uniformIcc : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

def spherePoint (c φ : ℝ) : E3 :=
  WithLp.toLp 2 ![Real.sqrt (1 - c ^ 2) * Real.cos φ, Real.sqrt (1 - c ^ 2) * Real.sin φ, c]

def zonalK (c₁ c₂ : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + max c₁ c₂) * (1 - min c₁ c₂) / 4)

def uMean (f : ℝ → ℝ) : ℝ := (1 / 2) * ∫ x in (-1 : ℝ)..1, f x

def centredPrimitive (f : ℝ → ℝ) (c : ℝ) : ℝ := ∫ t in (-1 : ℝ)..c, (f t - uMean f)

def bilinMean (g : MvPolynomial (Fin 2) ℝ) : ℝ :=
  ∑ d ∈ g.support, g.coeff d * uMean (fun x => x ^ d 0) * uMean (fun x => x ^ d 1)

def bilinCentred (g : MvPolynomial (Fin 2) ℝ) (c : ℝ) : ℝ :=
  ∑ d ∈ g.support, g.coeff d * centredPrimitive (fun x => x ^ d 0) c *
    centredPrimitive (fun x => x ^ d 1) c

def fibreIntegral (k : ℕ) (a : E3) : ℝ :=
  ∫ p : S2 × S2, logKernel (inner ℝ (p.1 : E3) (p.2 : E3)) *
    MvPolynomial.eval ![inner ℝ a (p.1 : E3), inner ℝ a (p.2 : E3)] (gMixed ℝ k)
    ∂(sphereProb.prod sphereProb)

def axis3 : E3 := EuclideanSpace.single 2 1

def fibreConst (k : ℕ) : ℝ := fibreIntegral k axis3

def pairPoly (k : ℕ) (n₁ n₂ : E3) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.bind₁
    ![∑ i, MvPolynomial.C (n₁.ofLp i) * MvPolynomial.X i,
      ∑ i, MvPolynomial.C (n₂.ofLp i) * MvPolynomial.X i] (gMixed ℝ k)

def momentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ D ∈ Finset.range (2 * k + 1), ∑ e ∈ (Finset.univ : Finset (Fin 3)).finsuppAntidiag D,
    MvPolynomial.monomial e
      (∫ p : S2 × S2, logKernel (inner ℝ (p.1 : E3) (p.2 : E3)) *
        (pairPoly k (p.1 : E3) (p.2 : E3)).coeff e ∂(sphereProb.prod sphereProb))

def ddcDensity (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  (2 / Real.pi) * (wirtinger (fun w : Fin 1 → ℂ =>
    wirtingerBar (fun u : Fin 1 → ℂ => ((f (u 0) : ℝ) : ℂ)) 0 w) 0 (fun _ => z)).re

def linFormPow (K : Type*) [Field K] (r D : ℕ) (ℓ : Fin r → K) :
    MvPolynomial.homogeneousSubmodule (Fin r) K D :=
  ⟨(∑ i, MvPolynomial.C (ℓ i) * MvPolynomial.X i) ^ D, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have h1 : (∑ i, MvPolynomial.C (ℓ i) * MvPolynomial.X i : MvPolynomial (Fin r) K).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _
    simpa using h1.pow D⟩

def UnipotentLeadingMinor.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (a : Fin N → Fin N → R) (l : ℕ) (hl : l ≤ N),
    ((unipotentMatrix a).submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1

def UnipotentCoordinates.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (a : Fin N → Fin N → R) (l m : Fin N), l < m →
    ((unipotentMatrix a).submatrix (Fin.castLE l.isLt) (minorColumns l m)).det = a m l

def PluckerFrameChange.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l N : ℕ) (V : Matrix (Fin l) (Fin N) R)
    (g : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), I.card = l →
    pluckerCoord (V * g) I =
      ∑ J ∈ (Finset.univ : Finset (Fin N)).powersetCard l, pluckerCoord V J * squareMinor l g J I

def GramSumOfMinors.Statement : Prop :=
  ∀ (l N : ℕ) (V : Matrix (Fin l) (Fin N) ℂ),
    ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard l, ((‖pluckerCoord V I‖ ^ 2 : ℝ) : ℂ) =
      (V * Vᴴ).det

def OmitStepPolynomial.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (p : LowerPairs N),
    letI := omitStepAlgebra R p
    ∃ e : MvPolynomial (LowerPairs N) R ≃ₐ[MvPolynomial {q // q ≠ p} R]
        Polynomial (MvPolynomial {q // q ≠ p} R),
      e (MvPolynomial.X p) = Polynomial.X

def LineQuotientDeterminant.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E], Module.finrank ℂ E = 2 →
    ∀ S : Submodule ℂ E, Module.finrank ℂ S = 1 → ∀ e ∈ S, e ≠ 0 → ∀ f : E,
      gramWedgeNorm e f = ‖e‖ * ‖S.mkQ f‖

def SectionLocalEquation.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (a₁ a₂ b₁ b₂ : R),
    Function.Bijective (fun r : R => r • (lineA a₂).mkQ (eps₂ R)) ∧
    (lineA a₂).mkQ (eps₁ R + a₁ • eps₂ R) = (a₁ - a₂) • (lineA a₂).mkQ (eps₂ R) ∧
    Function.Bijective (fun r : R => r • (lineB b₂).mkQ (eps₁ R)) ∧
    (lineB b₂).mkQ (b₁ • eps₁ R + eps₂ R) = (b₁ - b₂) • (lineB b₂).mkQ (eps₁ R) ∧
    (lineB b₂).mkQ (eps₁ R + a₁ • eps₂ R) = (1 - a₁ * b₂) • (lineB b₂).mkQ (eps₁ R)

def DiagonalQuotient.Statement : Prop :=
  ∀ (R : Type) [CommRing R],
    ((∃ e : diagQuot R ≃ₐ[R] Polynomial R,
        e (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = Polynomial.X ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = Polynomial.X) ∧
      (IsDomain R → IsDomain (diagQuot R)) ∧ Module.Flat R (diagQuot R)) ∧
    ((∃ e : crossQuot R ≃ₐ[R] LaurentPolynomial R,
        e (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = LaurentPolynomial.T 1 ∧
        e (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = LaurentPolynomial.T (-1)) ∧
      (IsDomain R → IsDomain (crossQuot R)) ∧ Module.Flat R (crossQuot R))

def DiagonalLocalDVR.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R],
    (∃ _ : (diagIdeal R).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (diagIdeal R)) ∧
      Irreducible (algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime (diagIdeal R))
        (MvPolynomial.X 0 - MvPolynomial.X 1))) ∧
    (∃ _ : (crossIdeal R).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (crossIdeal R)) ∧
      Irreducible (algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime (crossIdeal R))
        (1 - MvPolynomial.X 0 * MvPolynomial.X 1)))

def BlochOverlap.Statement : Prop :=
  ∀ e₁ e₂ : EuclideanSpace ℂ (Fin 2), ‖e₁‖ = 1 → ‖e₂‖ = 1 →
    ‖blochVector e₁‖ = 1 ∧
    ‖inner ℂ e₁ e₂‖ ^ 2 = (1 + inner ℝ (blochVector e₁) (blochVector e₂)) / 2

def SectionNormLog.Statement : Prop :=
  ∀ e₁ e₂ : EuclideanSpace ℂ (Fin 2), ‖e₁‖ = 1 → ‖e₂‖ = 1 →
    ‖(ℂ ∙ e₂).mkQ e₁‖ ^ 2 = 1 - ‖inner ℂ e₁ e₂‖ ^ 2 ∧
    (e₁ ∉ ℂ ∙ e₂ →
      Real.log ‖(ℂ ∙ e₂).mkQ e₁‖ = logKernel (inner ℝ (blochVector e₁) (blochVector e₂)))

def GKernelIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (k : ℕ),
    (MvPolynomial.X 0 + MvPolynomial.X 1) * gKernel R k =
      MvPolynomial.X 1 * (MvPolynomial.X 0 ^ (2 * k) - MvPolynomial.X 1 ^ (2 * k)) ∧
    (gKernel R k).IsHomogeneous (2 * k) ∧
    gKernelEval k (1 : R) 1 = 0 ∧ gKernelEval k (-1 : R) (-1) = 0 ∧
    gKernelEval k (1 : R) (-1) = -(2 * (k : R)) ∧ gKernelEval k (-1 : R) 1 = -(2 * (k : R)) ∧
    (∀ x : R, gKernelEval k x (-1) * (x - 1) = -(x ^ (2 * k) - 1)) ∧
    (∀ y : R, gKernelEval k (-1) y * (y - 1) = -(y * (y ^ (2 * k) - 1))) ∧
    (∀ c : R, gKernelEval k 1 c * (1 + c) = c * (1 - c ^ (2 * k))) ∧
    (∀ c : R, gKernelEval k c 1 * (c + 1) = c ^ (2 * k) - 1)

def MixedCoefficient.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (v₁ v₂ A₁ A₂ : R), v₁ ^ 2 = 0 → v₂ ^ 2 = 0 →
    ∀ G : MvPolynomial (Fin 2) R,
      MvPolynomial.eval ![A₁ - v₁, A₂ - v₂] G =
        MvPolynomial.eval ![A₁, A₂] G - v₁ * MvPolynomial.eval ![A₁, A₂] (MvPolynomial.pderiv 0 G)
          - v₂ * MvPolynomial.eval ![A₁, A₂] (MvPolynomial.pderiv 1 G)
          + v₁ * v₂ * MvPolynomial.eval ![A₁, A₂]
              (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 G))

def SphereHeightUniform.Statement : Prop :=
  ∀ u : E3, ‖u‖ = 1 → sphereProb.map (fun n : S2 => inner ℝ u (n : E3)) = uniformIcc

def SphereMoment.Statement : Prop :=
  ∀ (a : E3) (m : ℕ),
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m) ∂sphereProb = ‖a‖ ^ (2 * m) / (2 * m + 1) ∧
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m + 1) ∂sphereProb = 0

def FibrePushforward.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n : S2, inner ℝ a (n : E3) ^ (2 * k - 2) ∂sphereProb =
      -(inner ℝ a a ^ (k - 1))

def ZonalKernel.Statement : Prop :=
  ∀ c₁ c₂ : ℝ, c₁ ∈ Set.Icc (-1 : ℝ) 1 → c₂ ∈ Set.Icc (-1 : ℝ) 1 → c₁ ≠ c₂ →
    (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        logKernel (inner ℝ (spherePoint c₁ φ) (spherePoint c₂ 0)) = zonalK c₁ c₂

def ZonalBilinearFormula.Statement : Prop :=
  ∀ (F H : Polynomial ℝ) (u : E3), ‖u‖ = 1 →
    ∫ p : S2 × S2, logKernel (inner ℝ (p.1 : E3) (p.2 : E3)) * F.eval (inner ℝ u (p.1 : E3)) *
        H.eval (inner ℝ u (p.2 : E3)) ∂(sphereProb.prod sphereProb) =
      -(1 / 2) * uMean (fun x => F.eval x) * uMean (fun x => H.eval x) -
        (1 / 4) * ∫ c in (-1 : ℝ)..1,
          centredPrimitive (fun x => F.eval x) c * centredPrimitive (fun x => H.eval x) c /
            (1 - c ^ 2)

def GHatIdentity.Statement : Prop :=
  ∀ k : ℕ, bilinMean (gMixed ℝ k) = k ∧
    ∀ c : ℝ, bilinCentred (gMixed ℝ k) c = (1 - c ^ (2 * k)) - k * (1 - c ^ 2)

def FibreConstantClosedForm.Statement : Prop :=
  (∀ k : ℕ, 1 ≤ k → fibreConst k = -(1 / 2) * ∑ j ∈ Finset.Icc 1 k, 1 / (2 * (j : ℝ) - 1)) ∧
    -fibreConst 1 = 1 / 2 ∧ -fibreConst 2 = 2 / 3 ∧ -fibreConst 3 = 23 / 30 ∧
    -fibreConst 4 = 88 / 105 ∧ -fibreConst 5 = 563 / 630 ∧ -fibreConst 6 = 3254 / 3465

def FibreIntegralInvariant.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ a : E3, fibreIntegral k a = fibreConst k * inner ℝ a a ^ (k - 1)) ∧
    ∀ (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
      MvPolynomial.aeval a (momentPoly k) = algebraMap ℝ B (fibreConst k) * (∑ i, a i ^ 2) ^ (k - 1)

def CompactPairCurveForm.Statement : Prop :=
  (∀ z : ℂ, ddcDensity (fun w => Real.log (1 + ‖w‖ ^ 2) / 2) z = (1 / Real.pi) / (1 + ‖z‖ ^ 2) ^ 2) ∧
    ∫ z : ℂ, (1 / Real.pi) / (1 + ‖z‖ ^ 2) ^ 2 = 1

def BarCurveForm.Statement : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    ddcDensity (fun w => -(Real.log (1 - ‖w‖ ^ 2) / 2)) z = (1 / Real.pi) / (1 - ‖z‖ ^ 2) ^ 2 ∧
    0 < ddcDensity (fun w => -(Real.log (1 - ‖w‖ ^ 2) / 2)) z

def TorusInvariantDiagonal.Statement : Prop :=
  ∀ (T : Type) [Group T] (ι : Type) [Fintype ι] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) (b : Module.Basis ι ℂ V) (χ : ι → (T →* Circle)),
    (∀ t i, ρ t (b i) = ((χ i t : Circle) : ℂ) • b i) → Function.Injective χ →
    ∀ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ x y, B x y = conj (B y x)) →
      (∀ t x y, B (ρ t x) (ρ t y) = B x y) →
      ∀ i j, i ≠ j → B (b i) (b j) = 0

def TopPowerDiagonal.Statement : Prop :=
  ∀ (A : Type) [CommRing A] (D : ℕ) (ω lam : Fin D → A), (∀ j, ω j ^ 2 = 0) →
    (∑ j, lam j * ω j) ^ D = (D.factorial : A) * (∏ j, lam j) * ∏ j, ω j

def PolarisationDegreeD.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r D : ℕ)
    (φ ψ : MvPolynomial.homogeneousSubmodule (Fin r) K D →ₗ[K] K),
    (∀ ℓ : Fin r → K, φ (linFormPow K r D ℓ) = ψ (linFormPow K r D ℓ)) → φ = ψ

def torusExampleChar : Fin 2 → (Circle →* Circle) := ![1, MonoidHom.id Circle]

def torusExampleRep : Representation ℂ Circle (Fin 2 → ℂ) where
  toFun t := Matrix.toLin' (Matrix.diagonal fun i => ((torusExampleChar i t : Circle) : ℂ))
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusExampleChar, Matrix.diagonal]
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    funext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal, mul_assoc]

def torusExampleForm : (Fin 2 → ℂ) →ₗ⋆[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => conj (x 0) * y 0)
    (fun x x' y => by simp [add_mul]) (fun c x y => by simp [mul_assoc])
    (fun x y y' => by simp [mul_add]) (fun c x y => by simp; ring)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FlagBundles
