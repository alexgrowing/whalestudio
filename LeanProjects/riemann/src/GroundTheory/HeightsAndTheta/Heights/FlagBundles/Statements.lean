import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial MeasureTheory Finset
open scoped InnerProductSpace ComplexConjugate Matrix

noncomputable section

abbrev LowerPairs (N : ℕ) := {p : Fin N × Fin N // p.2 < p.1}

def unipotentMatrix {R : Type*} [CommRing R] {N : ℕ} (a : LowerPairs N → R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun l m => if h : l < m then a ⟨(m, l), h⟩ else if l = m then 1 else 0

def genericUnipotent (R : Type*) [CommRing R] (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (LowerPairs N) R) :=
  unipotentMatrix (fun p => X p)

def firstRows {R : Type*} {N : ℕ} (V : Matrix (Fin N) (Fin N) R) (l : ℕ) (hl : l ≤ N) :
    Matrix (Fin l) (Fin N) R :=
  V.submatrix (Fin.castLE hl) id

def leadingMinor {R : Type*} [CommRing R] {N : ℕ} (V : Matrix (Fin N) (Fin N) R) (l : ℕ)
    (hl : l ≤ N) : R :=
  (V.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def pluckerCoord {R : Type*} [CommRing R] {l N : ℕ} (V : Matrix (Fin l) (Fin N) R)
    (I : Finset (Fin N)) : R :=
  if h : I.card = l then (V.submatrix id (I.orderEmbOfFin h)).det else 0

def minorOn {R : Type*} [CommRing R] {N : ℕ} (g : Matrix (Fin N) (Fin N) R) (l : ℕ)
    (J I : Finset (Fin N)) : R :=
  if h : J.card = l ∧ I.card = l then
    (g.submatrix (J.orderEmbOfFin h.1) (I.orderEmbOfFin h.2)).det
  else 0

def UnipotentLeadingMinor.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (a : LowerPairs N → R) (l : ℕ) (hl : l ≤ N),
    leadingMinor (unipotentMatrix a) l hl = 1

def UnipotentCoordinates.Statement : Prop :=
  (∀ (R : Type) [CommRing R] (N : ℕ) (a : LowerPairs N → R) (m l : Fin N) (h : l < m),
    pluckerCoord (firstRows (unipotentMatrix a) (l.val + 1) l.isLt) (insert m (Finset.Iio l)) =
      a ⟨(m, l), h⟩) ∧
  (∀ (R : Type) [CommRing R] (N : ℕ),
    Algebra.adjoin R (Set.range fun x : Fin (N + 1) × Finset (Fin N) =>
        pluckerCoord (firstRows (genericUnipotent R N) x.1.val (Nat.le_of_lt_succ x.1.isLt)) x.2) =
      ⊤)

def PluckerFrameChange.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l N : ℕ) (V : Matrix (Fin l) (Fin N) R)
    (g : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), I.card = l →
    pluckerCoord (V * g) I =
      ∑ J ∈ Finset.powersetCard l (Finset.univ : Finset (Fin N)), pluckerCoord V J * minorOn g l J I

def GramSumOfMinors.Statement : Prop :=
  ∀ (l N : ℕ) (V : Matrix (Fin l) (Fin N) ℂ),
    (((∑ I ∈ Finset.powersetCard l (Finset.univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 : ℝ)) :
        ℂ) = (V * Vᴴ).det ∧
    ((V * Vᴴ).det ≠ 0 →
      ∑ I ∈ Finset.powersetCard l (Finset.univ : Finset (Fin N)),
        ‖pluckerCoord V I‖ ^ 2 / ‖(V * Vᴴ).det‖ = 1)

def OmitStepPolynomial.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (σ : Type) [DecidableEq σ] (p : σ),
    ∃ e : MvPolynomial σ R ≃+* Polynomial (MvPolynomial {q // q ≠ p} R),
      e (X p) = Polynomial.X ∧
      (∀ q : {q // q ≠ p}, e (X q.val) = Polynomial.C (X q)) ∧
      ∀ r : R, e (C r) = Polynomial.C (C r)

def LineQuotientDeterminant.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E], Module.finrank ℂ E = 2 →
    ∀ S : Submodule ℂ E, Module.finrank ℂ S = 1 → ∀ e ∈ S, e ≠ 0 → ∀ f : E,
      Real.sqrt (Matrix.gram ℂ ![e, f]).det.re = ‖e‖ * ‖(Submodule.Quotient.mk f : E ⧸ S)‖

def eps (R : Type*) [CommRing R] (i : Fin 2) : Fin 2 → R := Pi.single i 1

def SectionLocalEquation.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (a₁ a₂ b₁ b₂ : R),
    (let S := Submodule.span R {eps R 0 + a₂ • eps R 1}
     Function.Bijective (fun r : R => r • S.mkQ (eps R 1)) ∧
       S.mkQ (eps R 0 + a₁ • eps R 1) = (a₁ - a₂) • S.mkQ (eps R 1)) ∧
    (let S := Submodule.span R {b₂ • eps R 0 + eps R 1}
     Function.Bijective (fun r : R => r • S.mkQ (eps R 0)) ∧
       S.mkQ (b₁ • eps R 0 + eps R 1) = (b₁ - b₂) • S.mkQ (eps R 0) ∧
       S.mkQ (eps R 0 + a₁ • eps R 1) = (1 - a₁ * b₂) • S.mkQ (eps R 0))

def diagonalIdeal (R : Type*) [CommRing R] : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {X 0 - X 1}

def mixedDiagonalIdeal (R : Type*) [CommRing R] : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {1 - X 0 * X 1}

def DiagonalQuotient.Statement : Prop :=
  ∀ (R : Type) [CommRing R],
    (∃ e : (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) ≃ₐ[R] Polynomial R,
      e (Ideal.Quotient.mk _ (X 0)) = Polynomial.X ∧ e (Ideal.Quotient.mk _ (X 1)) = Polynomial.X) ∧
    Module.Flat R (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) ∧
    (IsDomain R → IsDomain (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R)) ∧
    (∃ e : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) ≃ₐ[R] LaurentPolynomial R,
      e (Ideal.Quotient.mk _ (X 0)) = LaurentPolynomial.T 1 ∧
        e (Ideal.Quotient.mk _ (X 1)) = LaurentPolynomial.T (-1)) ∧
    Module.Flat R (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) ∧
    (IsDomain R → IsDomain (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R))

def DiagonalLocalDVR.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R],
    (∃ hP : (diagonalIdeal R).IsPrime,
      IsDiscreteValuationRing (@Localization.AtPrime _ _ (diagonalIdeal R) hP) ∧
      Irreducible (algebraMap (MvPolynomial (Fin 2) R)
        (@Localization.AtPrime _ _ (diagonalIdeal R) hP) (X 0 - X 1))) ∧
    (∃ hP : (mixedDiagonalIdeal R).IsPrime,
      IsDiscreteValuationRing (@Localization.AtPrime _ _ (mixedDiagonalIdeal R) hP) ∧
      Irreducible (algebraMap (MvPolynomial (Fin 2) R)
        (@Localization.AtPrime _ _ (mixedDiagonalIdeal R) hP) (1 - X 0 * X 1)))

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

def blochVector (e : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => (star (WithLp.ofLp e) ⬝ᵥ (pauli i *ᵥ WithLp.ofLp e)).re

def kernelL (s : ℝ) : ℝ := (1 / 2) * Real.log ((1 - s) / 2)

def BlochOverlap.Statement : Prop :=
  (∀ e : EuclideanSpace ℂ (Fin 2), ‖e‖ = 1 → ‖blochVector e‖ = 1) ∧
  ∀ e₁ e₂ : EuclideanSpace ℂ (Fin 2), ‖e₁‖ = 1 → ‖e₂‖ = 1 →
    ‖⟪e₁, e₂⟫_ℂ‖ ^ 2 = (1 + ⟪blochVector e₁, blochVector e₂⟫_ℝ) / 2

def SectionNormLog.Statement : Prop :=
  ∀ e₁ e₂ : EuclideanSpace ℂ (Fin 2), ‖e₁‖ = 1 → ‖e₂‖ = 1 →
    ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖ ^ 2 = 1 - ‖⟪e₁, e₂⟫_ℂ‖ ^ 2 ∧
    (e₁ ∉ ℂ ∙ e₂ →
      Real.log ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖ =
        kernelL ⟪blochVector e₁, blochVector e₂⟫_ℝ)

def gKernel (R : Type*) [CommRing R] (k : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ j ∈ Finset.range k,
    (X 0 ^ (2 * j + 1) * X 1 ^ (2 * k - 1 - 2 * j) - X 0 ^ (2 * j) * X 1 ^ (2 * k - 2 * j))

def GKernelIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (k : ℕ),
    (X 0 + X 1) * gKernel R k = X 1 * (X 0 ^ (2 * k) - X 1 ^ (2 * k)) ∧
    (gKernel R k).IsHomogeneous (2 * k) ∧
    eval ![1, 1] (gKernel R k) = 0 ∧ eval ![-1, -1] (gKernel R k) = 0 ∧
    eval ![1, -1] (gKernel R k) = -(2 * k : R) ∧ eval ![-1, 1] (gKernel R k) = -(2 * k : R) ∧
    ∀ c : R,
      eval ![c, -1] (gKernel R k) * (c - 1) = -(c ^ (2 * k) - 1) ∧
      eval ![-1, c] (gKernel R k) * (c - 1) = -(c * (c ^ (2 * k) - 1)) ∧
      eval ![1, c] (gKernel R k) * (1 + c) = c * (1 - c ^ (2 * k)) ∧
      eval ![c, 1] (gKernel R k) * (c + 1) = c ^ (2 * k) - 1

def MixedCoefficient.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (G : MvPolynomial (Fin 2) S) (A₁ A₂ v₁ v₂ : S),
    v₁ ^ 2 = 0 → v₂ ^ 2 = 0 →
      eval ![A₁ - v₁, A₂ - v₂] G =
        eval ![A₁, A₂] G - v₁ * eval ![A₁, A₂] (pderiv 0 G) - v₂ * eval ![A₁, A₂] (pderiv 1 G) +
          v₁ * v₂ * eval ![A₁, A₂] (pderiv 0 (pderiv 1 G))

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev Sphere2 := Metric.sphere (0 : E3) 1

def sphereMeasure : Measure Sphere2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

def pairMeasure : Measure (Sphere2 × Sphere2) := sphereMeasure.prod sphereMeasure

def height (n : Sphere2) : ℝ := (n : E3) 2

def SphereHeightUniform.Statement : Prop :=
  ∀ u : E3, ‖u‖ = 1 →
    sphereMeasure.map (fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ) =
      (2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

def SphereMoment.Statement : Prop :=
  ∀ (a : E3) (m : ℕ),
    ∫ n, ⟪a, (n : E3)⟫_ℝ ^ (2 * m) ∂sphereMeasure = ‖a‖ ^ (2 * m) / (2 * m + 1) ∧
    ∫ n, ⟪a, (n : E3)⟫_ℝ ^ (2 * m + 1) ∂sphereMeasure = 0

def FibrePushforward.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n, ⟪a, (n : E3)⟫_ℝ ^ (2 * k - 2) ∂sphereMeasure = -(⟪a, a⟫_ℝ ^ (k - 1))

def spherePoint (c φ : ℝ) : E3 :=
  !₂[Real.sqrt (1 - c ^ 2) * Real.cos φ, Real.sqrt (1 - c ^ 2) * Real.sin φ, c]

def zonalKernel (c₁ c₂ : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + max c₁ c₂) * (1 - min c₁ c₂) / 4)

def ZonalKernel.Statement : Prop :=
  ∀ c₁ ∈ Set.Icc (-1 : ℝ) 1, ∀ c₂ ∈ Set.Icc (-1 : ℝ) 1, c₁ ≠ c₂ →
    (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = zonalKernel c₁ c₂

def uniformMean (F : ℝ → ℝ) : ℝ := (1 / 2) * ∫ t in (-1 : ℝ)..1, F t

def centredPrimitive (F : Polynomial ℝ) (c : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..c, (F.eval t - uniformMean F.eval)

def ZonalBilinearFormula.Statement : Prop :=
  (∀ F H : Polynomial ℝ,
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2) ∂pairMeasure =
      -(1 / 2) * uniformMean F.eval * uniformMean H.eval -
        (1 / 4) * ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2)) ∧
  ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * height p.1 * height p.2 ∂pairMeasure = -1 / 12

def gMixed (k : ℕ) : MvPolynomial (Fin 2) ℝ := pderiv 0 (pderiv 1 (gKernel ℝ k))

def squareMean (g : MvPolynomial (Fin 2) ℝ) : ℝ :=
  (1 / 4) * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, eval ![x, y] g

def doublyCentred (g : MvPolynomial (Fin 2) ℝ) (c : ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..c, ∫ t in (-1 : ℝ)..c,
    (eval ![s, t] g - (1 / 2) * (∫ x in (-1 : ℝ)..1, eval ![x, t] g) -
      (1 / 2) * (∫ y in (-1 : ℝ)..1, eval ![s, y] g) + squareMean g)

def GHatIdentity.Statement : Prop :=
  ∀ k : ℕ, squareMean (gMixed k) = k ∧
    ∀ c : ℝ, doublyCentred (gMixed k) c = (1 - c ^ (2 * k)) - k * (1 - c ^ 2)

def fibreConstant (k : ℕ) : ℝ :=
  ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * eval ![height p.1, height p.2] (gMixed k) ∂pairMeasure

def FibreConstantClosedForm.Statement : Prop :=
  (∀ k : ℕ, fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)) ∧
  -fibreConstant 1 = 1 / 2 ∧ -fibreConstant 2 = 2 / 3 ∧ -fibreConstant 3 = 23 / 30 ∧
  -fibreConstant 4 = 88 / 105 ∧ -fibreConstant 5 = 563 / 630 ∧ -fibreConstant 6 = 3254 / 3465

def fibrePoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  let Q : MvPolynomial (Fin 3) (Sphere2 × Sphere2 → ℝ) :=
    aeval (fun r : Fin 2 => ∑ i : Fin 3,
        X i * C (fun p : Sphere2 × Sphere2 => ((if r = 0 then p.1 else p.2 : Sphere2) : E3) i))
      (gMixed k)
  ∑ μ ∈ Q.support,
    monomial μ (∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * coeff μ Q p ∂pairMeasure)

def FibreIntegralInvariant.Statement : Prop :=
  (∀ (k : ℕ) (a : E3),
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ *
        eval ![⟪a, (p.1 : E3)⟫_ℝ, ⟪a, (p.2 : E3)⟫_ℝ] (gMixed k) ∂pairMeasure =
      fibreConstant k * ⟪a, a⟫_ℝ ^ (k - 1)) ∧
  ∀ (k : ℕ) (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (fibrePoly k) = algebraMap ℝ B (fibreConstant k) * (∑ i, a i ^ 2) ^ (k - 1)

def ddcDensity (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  (2 / Real.pi) *
    (wirtinger (fun w : Fin 1 → ℂ => wirtingerBar (fun u : Fin 1 → ℂ => ((f (u 0) : ℝ) : ℂ)) 0 w) 0
      (fun _ => z)).re

def CompactPairCurveForm.Statement : Prop :=
  (∀ f : ℂ → ℝ, ContDiff ℝ 2 f → ∀ z : ℂ,
    ddcDensity f z = (2 * Real.pi)⁻¹ * InnerProductSpace.laplacianWithin f Set.univ z) ∧
  (∀ z : ℂ, ddcDensity (fun w => (1 / 2) * Real.log (1 + ‖w‖ ^ 2)) z =
    Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2) ∧
  ∫ z : ℂ, Real.pi⁻¹ / (1 + ‖z‖ ^ 2) ^ 2 = 1

def BarCurveForm.Statement : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    ddcDensity (fun w => -((1 / 2) * Real.log (1 - ‖w‖ ^ 2))) z = Real.pi⁻¹ / (1 - ‖z‖ ^ 2) ^ 2 ∧
    0 < ddcDensity (fun w => -((1 / 2) * Real.log (1 - ‖w‖ ^ 2))) z

def TorusInvariantDiagonal.Statement : Prop :=
  ∀ (ι T V : Type) [Fintype ι] [DecidableEq ι] [Group T] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ T V) (L : ι → Submodule ℂ V) (χ : ι → T →* Circle),
    DirectSum.IsInternal L → (∀ i, Module.finrank ℂ (L i) = 1) → Function.Injective χ →
    (∀ i, ∀ v ∈ L i, ∀ t : T, ρ t v = ((χ i t : Circle) : ℂ) • v) →
    ∀ h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ x y, h y x = conj (h x y)) → (∀ t x y, h (ρ t x) (ρ t y) = h x y) →
      ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, h x y = 0

def TopPowerDiagonal.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (D : ℕ) (ω lam : Fin D → S), (∀ j, ω j ^ 2 = 0) →
    (∑ j, lam j * ω j) ^ D = (D.factorial : S) * (∏ j, lam j) * (∏ j, ω j)

def PolarisationDegreeD.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r D : ℕ) (φ ψ : MvPolynomial (Fin r) K →ₗ[K] K),
    (∀ c : Fin r → K, φ ((∑ i, C (c i) * X i) ^ D) = ψ ((∑ i, C (c i) * X i) ^ D)) →
    ∀ P : MvPolynomial (Fin r) K, P.IsHomogeneous D → φ P = ψ P

def exampleFamily : LowerPairs 2 → ℤ := fun _ => 5

theorem unipotentMatrix_exampleFamily : unipotentMatrix exampleFamily = !![1, 5; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix, exampleFamily]

theorem example_unipotent_hyps :
    (1 : ℕ) ≤ 2 ∧ (0 : Fin 2) < 1 ∧ ({1} : Finset (Fin 2)).card = 1 :=
  ⟨by norm_num, by decide, rfl⟩

theorem gKernel_one : gKernel ℤ 1 = X 0 * X 1 - X 1 ^ 2 := by
  simp [gKernel]

theorem norm_single_zero : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by
  simp

theorem norm_single_one : ‖EuclideanSpace.single (1 : Fin 2) (1 : ℂ)‖ = 1 := by
  simp

theorem example_lineQuotientDeterminant_hyps :
    Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 ∧
    Module.finrank ℂ (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) = 1 ∧
    EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ∈ ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ∧
    EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ≠ 0 := by
  have hne : EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_single_zero]; exact one_ne_zero
  exact ⟨finrank_euclideanSpace_fin, finrank_span_singleton hne,
    Submodule.mem_span_singleton_self _, hne⟩

theorem example_diagonal_hyps : IsDomain ℤ ∧ IsNoetherianRing ℤ := ⟨inferInstance, inferInstance⟩

theorem example_sectionNormLog_hyps :
    ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 ∧ ‖EuclideanSpace.single (1 : Fin 2) (1 : ℂ)‖ = 1 ∧
    EuclideanSpace.single (0 : Fin 2) (1 : ℂ) ∉ ℂ ∙ EuclideanSpace.single (1 : Fin 2) (1 : ℂ) := by
  refine ⟨norm_single_zero, norm_single_one, ?_⟩
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 0) ha
  simp at h

abbrev SqZeroRing := MvPolynomial (Fin 2) ℚ ⧸ (Ideal.span {X 0 ^ 2, X 1 ^ 2} : Ideal (MvPolynomial (Fin 2) ℚ))

def sqZeroGen (r : Fin 2) : SqZeroRing := Ideal.Quotient.mk _ (X r)

theorem sqZeroGen_sq (r : Fin 2) : sqZeroGen r ^ 2 = 0 := by
  rw [sqZeroGen, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by fin_cases r <;> simp)

theorem sphereMeasure_univ : sphereMeasure Set.univ = 1 := by
  have h0 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (Metric.measure_ball_pos volume (0 : E3) one_pos).ne'
    simp
  have h1 : (volume : Measure E3).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  rw [sphereMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

theorem example_sphereHeightUniform_hyp : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
  simp

theorem example_fibre_hyps :
    1 ≤ 1 ∧ (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧ (1 / 2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧ (0 : ℝ) ≠ 1 / 2 := by
  refine ⟨le_rfl, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num⟩

theorem example_curveForm_hyps : ContDiff ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) ∧ ‖(0 : ℂ)‖ < 1 :=
  ⟨contDiff_norm_sq ℝ, by simp⟩

def exampleChar : Fin 2 → Circle →* Circle := ![1, MonoidHom.id Circle]

def exampleRep : Representation ℂ Circle (Fin 2 → ℂ) where
  toFun t := Matrix.toLin' (Matrix.diagonal fun j => ((exampleChar j t : Circle) : ℂ))
  map_one' := by
    ext v j
    simp
  map_mul' s t := by
    ext v j
    by_cases h : j = v
    · subst h; simp
    · simp [h]

def exampleLine (i : Fin 2) : Submodule ℂ (Fin 2 → ℂ) := ℂ ∙ Pi.basisFun ℂ (Fin 2) i

def exampleForm : (Fin 2 → ℂ) →ₗ⋆[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∑ i, conj (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp; ring)
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp; ring)

theorem example_torusInvariantDiagonal_hyps :
    DirectSum.IsInternal exampleLine ∧ (∀ i, Module.finrank ℂ (exampleLine i) = 1) ∧
    Function.Injective exampleChar ∧
    (∀ i, ∀ v ∈ exampleLine i, ∀ t : Circle, exampleRep t v = ((exampleChar i t : Circle) : ℂ) • v) ∧
    (∀ x y, exampleForm y x = conj (exampleForm x y)) ∧
    (∀ t x y, exampleForm (exampleRep t x) (exampleRep t y) = exampleForm x y) := by
  refine ⟨?_, fun i => finrank_span_singleton ((Pi.basisFun ℂ (Fin 2)).ne_zero i), ?_, ?_, ?_, ?_⟩
  · refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Pi.basisFun ℂ (Fin 2)).linearIndependent.iSupIndep_span_singleton ?_
    show ⨆ i, ℂ ∙ Pi.basisFun ℂ (Fin 2) i = ⊤
    rw [← Submodule.span_range_eq_iSup, Module.Basis.span_eq]
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · have := DFunLike.congr_fun h (Circle.exp Real.pi)
      have h2 := congrArg (fun z : Circle => (z : ℂ)) this
      simp [exampleChar, Circle.coe_exp] at h2
      norm_num at h2
    · have := DFunLike.congr_fun h (Circle.exp Real.pi)
      have h2 := congrArg (fun z : Circle => (z : ℂ)) this
      simp [exampleChar, Circle.coe_exp] at h2
      norm_num at h2
    · rfl
  · intro i v hv t
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    ext j
    simp [exampleRep, Pi.single_apply]
    split_ifs with hj
    · subst hj; ring
    · simp
  · intro x y
    simp [exampleForm, mul_comm]
  · intro t x y
    have hc : ∀ z : Circle, conj (z : ℂ) * z = 1 := fun z => by
      rw [Complex.conj_mul', Circle.norm_coe]; simp
    simp only [exampleForm, exampleRep, LinearMap.mk₂'ₛₗ_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.toLin'_apply, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (conj (x i) * y i) * hc (exampleChar i t)

theorem example_polarisation_hyp :
    ∀ c : Fin 2 → ℚ, MvPolynomial.lcoeff ℚ (Finsupp.single 0 2) ((∑ i, C (c i) * X i) ^ 2) =
      MvPolynomial.lcoeff ℚ (Finsupp.single 0 2) ((∑ i, C (c i) * X i) ^ 2) := fun _ => rfl

end

end GroundTheory.Heights₂.Heights.FlagBundles
