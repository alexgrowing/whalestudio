import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoordinateSecondPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Filter Topology
  Asymptotics
open scoped Manifold ContDiff ENNReal

noncomputable section

def ChangeOfLattice.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ)
    (m m' : ConeMetric ℂ (Ix κ)) (A : Matrix (Ix κ) (Ix κ) ℚ) (II : AllFam)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin D → ℂ) M] [IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (f : M → Ix κ → ℂ) (dV : Measure M),
    II.IsFamily → 1 ≤ D → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x →
    IsSmoothHerm (HermLine.ofCone m) → IsAnalyticRes (coordIdeal ℤ x) D f → IsSmoothVolume D dV →
    IsInvMat A → (∀ z, m'.ρ (matActC A z) = m.ρ z) →
    ((∀ i, x i ∈ Submodule.span ℤ (Set.range (matAct A x))) →
      (fun n : ℕ ↦ Real.log (latIndex x (matAct A x) n) -
          (top II (matAct A x) m' D - top II x m D) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
        =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D) ∧
    (fun n : ℕ ↦ defect II D (matAct A x) m' ((symMeasure f dV).map (matActC A)) n -
        defect II D x m (symMeasure f dV) n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D

def ProjectionBounds.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)) (II : AllFam)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin D → ℂ) M] [IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (f : M → Ix κ → ℂ) (dV : Measure M),
    II.IsFamily → 1 ≤ D → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x →
    IsProjFrame x e → IsPullFS x e m → IsAnalyticRes (coordIdeal ℤ x) D f → IsSmoothVolume D dV →
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω) (C : ℝ),
      (∀ l, ε l ∈ sec ℤ x k) ∧ LinearIndependent (fnField (x ∘ e)) ε ∧
      (∀ (n : ℕ) (p : Fin (projDeg x e) → Ω), (∀ l, p l ∈ sec ℤ (x ∘ e) n) →
        ∑ l, p l * ε l = 0 → p = 0) ∧
      (∀ n : ℕ, ∀ s ∈ sec ℤ x n, ∀ l, secTrace x e (n + k) (s * ε l) ∈ sec ℤ (x ∘ e) (n + k)) ∧
      (∀ n : ℕ, ∀ s ∈ sec ℤ x n, (∀ l, secTrace x e (n + k) (s * ε l) = 0) → s = 0) ∧
      ((fun n : ℕ ↦ (secRank x n : ℝ) - (projDeg x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
        =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (D - 1)) ∧
      (∀ (n : ℕ) (p : Fin (projDeg x e) → Ω), 1 ≤ n → (∀ l, p l ∈ sec ℤ (x ∘ e) n) →
        secNorm x m (symMeasure f dV) (n + k) (∑ l, p l * ε l) ≤
          C * (n : ℝ) ^ ((D : ℝ) / 2) *
            Real.sqrt (∑ l, secNorm (x ∘ e) (fsMetric (Fin (D + 1))) (sphProb (D + 1)) n (p l) ^ 2)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ s ∈ sec ℤ x n,
        Real.sqrt (∑ l, secNorm (x ∘ e) (fsMetric (Fin (D + 1))) (sphProb (D + 1)) (n + k)
            (secTrace x e (n + k) (s * ε l)) ^ 2) ≤
          C * (n : ℝ) ^ ((D : ℝ) / 2) * secNorm x m (symMeasure f dV) n s) ∧
      (∀ n : ℕ, k ≤ n →
        (projDeg x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) ≤
            chi x m (symMeasure f dV) n ∧
          chi x m (symMeasure f dV) n ≤
            (projDeg x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) ∧
      (fun n : ℕ ↦ defect II D x m (symMeasure f dV) n -
          (projDeg x e : ℝ) * hsDefect D (chiP D) (hhOf II D) n)
        =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

def MonomialDegree.Statement : Prop :=
  ∀ D : ℕ,
    (∀ a b : Fin (D + 1) → ℕ, ∑ i, a i = ∑ i, b i → a ≠ b →
      ∫ w, monoC a w * starRingEnd ℂ (monoC b w) ∂sphProb (D + 1) = 0) ∧
    (∀ a : Fin (D + 1) → ℕ, ∫ w, ‖monoC a w‖ ^ 2 ∂sphProb (D + 1) = monoNormSq a) ∧
    (∀ a : Fin (D + 1) → ℕ, monoNormSq (Function.update a 0 (a 0 + 1)) / monoNormSq a =
      ((a 0 : ℝ) + 1) / ((∑ i, a i : ℕ) + D + 1 : ℝ)) ∧
    (∀ n : ℕ, 0 ≤ chiP D n) ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → chiP D n ≤ C * (n : ℝ) ^ (D + 1) ∧ 0 ≤ chiP D (n + 1) - chiP D n ∧
      chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

def ReductionToProjective.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ)
    (m : ConeMetric ℂ (Ix κ)) (P₀ : Ideal (MvPolynomial (Ix κ) ℤ)) (II : AllFam)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin D → ℂ) M] [IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (f : M → Ix κ → ℂ) (dV : Measure M),
    II.IsFamily → IsHSDatum D x m P₀ → IsAnalyticRes (coordIdeal ℤ x) D f → IsSmoothVolume D dV →
    (fun n : ℕ ↦ defect II D x m (symMeasure f dV) n -
        geomDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) (HermLine.ofCone m) D *
          hsDefect D (chiP D) (hhOf II D) n) =o[atTop] pw D

def HilbertSamuelProjective.Statement : Prop :=
  ∀ (D : ℕ) (II : AllFam), II.IsFamily → 1 ≤ D → hsDefect D (chiP D) (hhOf II D) =o[atTop] pw D

def TheoremHSM.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ)
    (m : ConeMetric ℂ (Ix κ)) (P₀ : Ideal (MvPolynomial (Ix κ) ℤ)) (II : AllFam)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin D → ℂ) M] [IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (f : M → Ix κ → ℂ) (dV : Measure M),
    II.IsFamily → IsHSDatum D x m P₀ → IsAnalyticRes (coordIdeal ℤ x) D f → IsSmoothVolume D dV →
    defect II D x m (symMeasure f dV) =o[atTop] pw D ∧
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ g : MvPolynomial (Ix κ) ℂ, g.IsHomogeneous n →
        ∀ z ∈ pts (coordIdeal ℤ x),
          ptNorm m (RingHom.id ℂ) n g z ≤
            C * (n : ℝ) ^ ((D : ℝ) / 2) * l2Norm m (RingHom.id ℂ) (symMeasure f dV) n g

def SlopeLowerBound.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ)
    (m : ConeMetric ℂ (Ix κ)) (P₀ : Ideal (MvPolynomial (Ix κ) ℤ)) (II : AllFam)
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin D → ℂ) M] [IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (f : M → Ix κ → ℂ) (dV : Measure M),
    II.IsFamily → IsHSDatum D x m P₀ → IsAnalyticRes (coordIdeal ℤ x) D f → IsSmoothVolume D dV →
    ∃ g : ℕ → ℝ, g =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 1 ≤ n →
      top II x m D * n / ((D + 1) * geomDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) (HermLine.ofCone m) D) - g n ≤
        chi x m (symMeasure f dV) n / secRank x n

def IntegralClosureFinite.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix κ → Ω) (D : ℕ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → Birational (ι := GlobalTheory κ) x →
    (∃ (k : ℕ) (c : Ω), c ∈ sec ℤ x k ∧ c ≠ 0 ∧ ∀ n : ℕ, ∀ s ∈ secNm ℤ x n, c * s ∈ sec ℤ x (n + k)) ∧
    ((∀ j : Ix κ, x j ≠ 0 →
        IsIntegrallyClosed (Algebra.adjoin ℚ (Set.range fun i : Ix κ ↦ x i / x j))) →
      ∃ (N n₀ : ℕ), 1 ≤ N ∧ ∀ n : ℕ, n₀ ≤ n → ∀ s ∈ secNm ℤ x n, (N : Ω) * s ∈ sec ℤ x n)

def fsBundle {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (b : K → ℕ) : HermLine ι :=
  HermLine.ofMetrics (fun k ↦ fsMetric (ι k)) fun k ↦ (b k : ℤ)

def G1.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k ↦ (a k : ℤ)) → P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) A →
    MonomialsBounded (mCoordIdeal y) A a → IsConjInvariantH A →
    (∃ C : ℝ, ∀ n : ℕ, (chartLat y A.a n : Set Ω) ⊆ AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧
          SupLE (mCoordIdeal y) y ((n : ℤ) • A.a) (fun z ↦ A.h z ^ n) C s}) ∧
      0 ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ A)

def SuccessiveMinimaDual.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P₀ : Ideal (MRing ι)) (Λ : ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k ↦ (a k : ℤ)) → P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) A →
    IsConjInvariantH A → 0 < Λ →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) →
      ‖∏ p, z p ^ μ p‖ ≤ Λ * A.h z) →
    (∃ (C : ℝ) (k₀ : ℕ), ∀ n : ℕ, (chartLat y A.a n : Set Ω) ⊆ AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧ SupLE (mCoordIdeal y) y ((n : ℤ) • A.a) (fun z ↦ A.h z ^ n)
          (C * max (Λ ^ n) (Λ ^ (n - k₀))) s}) ∧
      0 ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ A) +
        ((D + 1 : ℕ) : ℝ) * Real.log Λ * geomDeg (mCoordIdeal y) A D

def G2.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb : HermLine ι) (b : K → ℕ) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → IsBig y Mb.a D → (∀ k, 1 ≤ b k) →
    ∃ (k : ℕ) (e : Ω) (C : ℝ), 1 ≤ k ∧ e ≠ 0 ∧ 0 ≤ C ∧
      e ∈ chartLat y ((k : ℤ) • Mb.a - (fsBundle b : HermLine ι).a) 1 ∧
      SupLE (mCoordIdeal y) y ((k : ℤ) • Mb.a - (fsBundle b : HermLine ι).a)
        (fun z ↦ Mb.h z ^ k / (fsBundle b : HermLine ι).h z) (Real.exp C) e ∧
      (∀ p q : ℕ, 1 ≤ p → k * p < q →
        IsSemipositiveRel P₀ (mCoordIdeal y) ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)) ∧
        IsAmpleGeneric (mCoordIdeal y) ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)) ∧
        IsAmpleOnFibres (mCoordIdeal y) ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)).a ∧
        ∀ (n : ℕ) (s : Ω) (c : ℝ),
          s ∈ chartLat y ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)).a n →
          s * e ^ (n * p) ∈ chartLat y Mb.a (n * q) ∧
          (SupLE (mCoordIdeal y) y ((n : ℤ) • ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)).a)
              (fun z ↦ ((hpow Mb (q - k * p)).tensor (hpow (fsBundle b) p)).h z ^ n) c s →
            SupLE (mCoordIdeal y) y (((n * q : ℕ) : ℤ) • Mb.a) (fun z ↦ Mb.h z ^ (n * q))
              (c * Real.exp (n * p * C)) (s * e ^ (n * p)))) ∧
      Tendsto (fun q : ℕ ↦ II K ι (mCoordIdeal y) (D + 1)
          (fun _ ↦ (hpow Mb (q - k)).tensor (fsBundle b)) / (q : ℝ) ^ (D + 1)) atTop
        (𝓝 (II K ι (mCoordIdeal y) (D + 1) fun _ ↦ Mb)) ∧
      Tendsto (fun q : ℕ ↦ geomDeg (mCoordIdeal y) ((hpow Mb (q - k)).tensor (fsBundle b)) D /
          (q : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) Mb D))

def G3.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb L : HermLine ι) (a : ℕ) (ιn : ℕ → Ω →+ Ω) (P₀ : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → IsBig y Mb.a D → IsSmallGenerated y D P₀ L →
    IsConjInvariantH L → 1 ≤ a →
    (∀ n : ℕ, a ∣ n → ∀ s ∈ chartLat y Mb.a n, ιn n s ∈ chartLat y L.a n) →
    (∀ n : ℕ, a ∣ n → ∀ s ∈ chartLat y Mb.a n, ιn n s = 0 → s = 0) →
    (∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → a ∣ n → ∃ U : Set ((Σ k, ι k) → ℂ), IsOpen U ∧
      mcPts (mCoordIdeal y) ⊆ closure (U ∩ mcPts (mCoordIdeal y)) ∧
      ∀ z ∈ U ∩ mcPts (mCoordIdeal y), ∀ s ∈ chartLat y Mb.a n,
        PtDominated y ((n : ℤ) • Mb.a) ((n : ℤ) • L.a) (fun z ↦ Mb.h z ^ n) (fun z ↦ L.h z ^ n)
          (Real.exp (n * η)) s (ιn n s) z) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ L)

def ArithmeticVolumeMultiplicative.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb L : HermLine ι) (a : ℕ) (ιn : ℕ → Ω →+ Ω) (P₀ : Ideal (MRing ι))
    (Λ t : ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → IsBig y Mb.a D →
    (∀ k, 0 ≤ L.a k) → IsSemipositiveRel P₀ (mCoordIdeal y) L → IsConjInvariantH L → IsBig y L.a D →
    0 < Λ → (∃ (q : ℕ) (w : Fin q → MRing ι), (∀ j, IsMultiHomog (w j) fun k ↦ (L.a k).toNat) ∧
      (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → mCoordIdeal y ≤ Q → ∃ j, w j ∉ Q) ∧
      ∀ j, ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ Λ * L.h z) →
    Real.log Λ ≤ t → 1 ≤ a →
    (∀ n : ℕ, a ∣ n → ∀ s ∈ chartLat y Mb.a n, ιn n s ∈ chartLat y L.a n) →
    (∀ n : ℕ, a ∣ n → ∀ s ∈ chartLat y Mb.a n, ιn n s = 0 → s = 0) →
    (∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → a ∣ n → ∃ U : Set ((Σ k, ι k) → ℂ), IsOpen U ∧
      mcPts (mCoordIdeal y) ⊆ closure (U ∩ mcPts (mCoordIdeal y)) ∧
      ∀ z ∈ U ∩ mcPts (mCoordIdeal y), ∀ s ∈ chartLat y Mb.a n,
        PtDominated y ((n : ℤ) • Mb.a) ((n : ℤ) • L.a) (fun z ↦ Mb.h z ^ n) (fun z ↦ L.h z ^ n)
          (Real.exp (n * (t + η))) s (ιn n s) z) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ L) + ((D + 1 : ℕ) : ℝ) * geomDeg (mCoordIdeal y) L D * t

def G4.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → IsBig y Mb.a D →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) →
    ∃ (n : ℕ) (s : Ω) (c : ℝ), 1 ≤ n ∧ s ∈ chartLat y Mb.a n ∧ s ≠ 0 ∧ c < 1 ∧
      SupLE (mCoordIdeal y) y ((n : ℤ) • Mb.a) (fun z ↦ Mb.h z ^ n) c s

def G5.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P₀ : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P₀ ≤ P → IsSemipositiveRel P₀ P A →
    IsConjInvariantH A → NefOnFibres P A.a →
    (∀ W : Ideal (MRing ι), IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]) →
    ∀ (W : Ideal (MRing ι)) (d : ℕ), IsArithVar W d → P ≤ W → 0 ≤ II K ι W d (fun _ ↦ A)

def G6.Statement : Prop :=
  (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsGoodDatum y D P₀ A → IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ A) ≤ volHat y A D) ∧
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → IsBig y Mb.a D →
    II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) ≤ volHat y Mb D

def ArithmeticVolumeBig.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a →
    II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) ≤ volHat y Mb D

def ArithmeticVolumeBigRefined.Statement : Prop := BirationalPullbackPushforwardFormula

def G7.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsGoodDatum y D P₀ A → IsSmallGenerated y D P₀ A → IsConjInvariantH A →
    limsup (fun n : ℕ ↦ hHat0 y A n / ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
        II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ A) ∧
      Tendsto (fun n : ℕ ↦ hHat0 y A n / ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop
        (𝓝 (II K ι (mCoordIdeal y) (D + 1) fun _ ↦ A))

def ArithmeticVolumeNef.Statement : Prop := ArithmeticHilbertSamuelUpperBound

def ArithmeticVolumeNefDual.Statement : Prop := ArithmeticHilbertSamuelUpperBoundNumberField

def Lift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsAmpleGeneric (mCoordIdeal y) A →
    IsAmpleOnFibres (mCoordIdeal y) A.a →
    ∃ j : ℕ, 1 ≤ j ∧ IsGeneratedOnModel y ((j : ℤ) • A.a) ∧ IsVeryAmpleGeneric y ((j : ℤ) • A.a)

def LiftPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (c : K → ℕ) (b' p : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → NefOnFibres (mCoordIdeal y) a → (∀ k, 1 ≤ c k) → 1 ≤ p →
    ∃ j : ℕ, 1 ≤ j ∧
      IsGeneratedOnModel y ((j : ℤ) • ((b' : ℤ) • a + (p : ℤ) • fun k ↦ (c k : ℤ))) ∧
      IsVeryAmpleGeneric y ((j : ℤ) • ((b' : ℤ) • a + (p : ℤ) • fun k ↦ (c k : ℤ)))

def Perturb.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (b : K → ℕ) (P₀ : Ideal (MRing ι)) (p q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → IsSmallGenerated y D P₀ L → (∀ k, 1 ≤ b k) → 1 ≤ p → 1 ≤ q →
    IsAmpleGeneric (mCoordIdeal y) ((hpow L q).tensor (hpow (fsBundle b) p)) ∧
      IsAmpleOnFibres (mCoordIdeal y) ((hpow L q).tensor (hpow (fsBundle b) p)).a ∧
      IsSmallGenerated y D P₀ ((hpow L q).tensor (hpow (fsBundle b) p))

def LatticeWithoutBigness.Statement : Prop :=
  SuccessiveMinimaUpperBound ∧
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (Mb : HermLine ι) (P₀ : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P₀ ≤ mCoordIdeal y → IsSemipositiveRel P₀ (mCoordIdeal y) Mb → IsConjInvariantH Mb →
    NefOnFibres (mCoordIdeal y) Mb.a → 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ ↦ Mb) →
    ∃ (n : ℕ) (s : Ω) (c : ℝ), 1 ≤ n ∧ s ∈ chartLat y Mb.a n ∧ s ≠ 0 ∧ c < 1 ∧
      SupLE (mCoordIdeal y) y ((n : ℤ) • Mb.a) (fun z ↦ Mb.h z ^ n) c s

section Inhabitants

open P1 ComplexProjectiveLineResolution GroundTheory.Heights₂.Heights.CP

def idMaps : ℕ → Fld →+ Fld := fun _ ↦ AddMonoidHom.id Fld

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
