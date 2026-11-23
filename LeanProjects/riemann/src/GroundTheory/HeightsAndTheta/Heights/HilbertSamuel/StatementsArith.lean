import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.DefectSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHSRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory
  Topology

noncomputable section

set_option linter.unusedSectionVars false

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def genDeg (P : Ideal (MRing ι)) (D : ℕ) (a : K → ℤ) : ℤ :=
  GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => a)

def fibreIdeal {Ω : Type} [Field Ω] (ℓ : ℕ) (y : (Σ k, ι k) → Ω) : Ideal (MRingOver (ZMod ℓ) ι) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))

def IsBoundedH {Ω : Type} [Field Ω] (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ)
    (c : ℝ) (s : Ω) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

def HermLine.zcomb (A B : HermLine ι) (p q : ℤ) : HermLine ι where
  a := p • A.a + q • B.a
  h z := A.h z ^ p * B.h z ^ q
  pos z hz := mul_pos (zpow_pos (A.pos z hz) p) (zpow_pos (B.pos z hz) q)
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc, mul_zpow, mul_zpow, ← Finset.prod_zpow, ← Finset.prod_zpow]
    have : ∀ k, (‖c k‖ ^ A.a k) ^ p * (‖c k‖ ^ B.a k) ^ q = ‖c k‖ ^ (p • A.a + q • B.a) k := by
      intro k
      have hck : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hck]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf
    rw [← Finset.prod_congr rfl fun k _ => this k, Finset.prod_mul_distrib]
    ring

def fsH (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) 1

structure IsSmallGeneratedDatum {Ω : Type} [Field Ω] (P0 : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (D : ℕ)
    (A : HermLine ι) : Prop where
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P0 (mCoordIdeal y) A
  deg_pos : 0 < genDeg (mCoordIdeal y) D A.a
  gen : ∃ (q : ℕ) (w : Fin q → Ω), (∀ j, w j ∈ chartLat y A.a 1) ∧ KH.GeneratesOn y A.a w ∧
    ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)

structure IsNefBigDatum {Ω : Type} [Field Ω] (P0 : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (D : ℕ)
    (M : HermLine ι) : Prop where
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P0 (mCoordIdeal y) M
  conjInv : IsConjInvariantH M
  nef : NefOnFibres (mCoordIdeal y) M.a
  big : 0 < genDeg (mCoordIdeal y) D M.a

def PtBoundOn {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (M L' : HermLine ι) (n : ℕ) (U : Set ((Σ k, ι k) → ℂ))
    (c : ℝ) (f f' : Ω) : Prop :=
  ∀ (dg dh dg' dh' : K → ℕ) (g h g' h' : MRing ι),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * M.a k) → aeval y g = f * aeval y h →
    IsMultiHomog g' dg' → IsMultiHomog h' dh' → (∀ k, (dg' k : ℤ) = dh' k + n * L'.a k) →
    aeval y g' = f' * aeval y h' → ∀ z ∈ U,
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 → eval z (map (Int.castRingHom ℂ) h') ≠ 0 →
    ‖eval z (map (Int.castRingHom ℂ) g')‖ / (‖eval z (map (Int.castRingHom ℂ) h')‖ * L'.h z ^ n) ≤
      c * (‖eval z (map (Int.castRingHom ℂ) g)‖ / (‖eval z (map (Int.castRingHom ℂ) h)‖ * M.h z ^ n))

def IsBoundedHOver {Ω : Type} [Field Ω] {F : Type} [Field F] [Algebra F Ω] (P : Ideal (MRing ι))
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (c : (F →+* ℂ) → ℝ) (s : Ω) : Prop :=
  ∀ (sg : F →+* ℂ) (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P → LiesOver y sg z →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c sg * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

end Objects

theorem coordIdeal_eq_mCoordIdeal {Ω : Type} [Field Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω) : coordIdeal ℤ x = mCoordIdeal (ι := GlobalTheory κ) x := by
  have key : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars ℤ).comp
      (mConeMap (ι := GlobalTheory κ) x) = coneMap ℤ x := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, coneMap]
  ext f
  show f ∈ RingHom.ker (coneMap ℤ x) ↔ f ∈ RingHom.ker (mConeMap (ι := GlobalTheory κ) x)
  rw [RingHom.mem_ker, RingHom.mem_ker, ← key]
  exact map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective

section OneBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

structure IsGoodDatum (D : ℕ) (x : Ix κ → Ω) (m : ConeMetric ℂ (Ix κ)) : Prop where
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  smooth : IsSmoothMetric m
  conjInv : IsConjInvariant m
  semipos : ∃ P0 : Ideal (MRing (GlobalTheory κ)), P0 ≤ coordIdeal ℤ x ∧
    IsSemipositiveRel P0 (coordIdeal ℤ x) (HermLine.ofCone m)

def latLogIndex (x x' : Ix κ → Ω) (n : ℕ) : ℝ :=
  Real.log ((sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup) -
    Real.log ((sec ℤ x' n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup)

end OneBlock

def gaussMeasure (J : Type) [Fintype J] : Measure (J → ℂ) :=
  volume.withDensity fun z =>
    ENNReal.ofReal (Real.pi ^ (-(Fintype.card J : ℤ)) * Real.exp (-∑ j, ‖z j‖ ^ 2))

section BlockBirationality

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def BlockBirational (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  ∀ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d → IsMultiHomog h d → aeval y h ≠ 0 →
    ∃ (n : ℕ) (g' h' : MRing ι), IsMultiHomog g' (blockDeg k₀ n) ∧ IsMultiHomog h' (blockDeg k₀ n) ∧
      aeval y h' ≠ 0 ∧ aeval y g * aeval y h' = aeval y g' * aeval y h

end BlockBirationality

set_option maxHeartbeats 2000000 in

structure HSMBlockDatum (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] where

  y : (Σ k, ι k) → Ω

  k₀ : K

  A : HermLine ι

  P0 : Ideal (MRing ι)

  J : Ideal (MRing ι)

  R : AnRes (mCoordIdeal y) J D
  [meas : MeasurableSpace R.X]
  [borel : BorelSpace R.X]

  dV : Measure R.X
  one_le : 1 ≤ D
  arith : IsArithVar (mCoordIdeal y) (D + 1)
  birat : BlockBirational y k₀
  deg : A.a = unitDeg k₀
  conjInv : IsConjInvariantH A
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ mCoordIdeal y

  semipos : IsSemipositiveRel P0 (mCoordIdeal y) A
  vol : IsSmoothVolume R.A dV

attribute [instance] HSMBlockDatum.meas HSMBlockDatum.borel

section Block

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockPt (d : HSMBlockDatum D K ι Ω) (x : d.R.X) : (Σ k, ι k) → ℂ := d.R.lift x x

def pairValH (A : HermLine ι) (n : ℕ) (b b' : MvPolynomial (Σ k, ι k) ℚ) (z : (Σ k, ι k) → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b) * starRingEnd ℂ (eval z (map (algebraMap ℚ ℂ) b')) /
    ((A.h z ^ (2 * n) : ℝ) : ℂ)

def blockGram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) * ((∫ x, pairValH d.A n (b k) (b l) (blockPt d x) ∂d.dV).re +
    (∫ x, pairValH d.A n (b k) (b l) (conjPt (blockPt d x)) ∂d.dV).re)

open Classical in

def blockChi (d : HSMBlockDatum D K ι Ω) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2 then
    -(1 / 2) * Real.log (blockGram d n h.choose.2).det
  else 0

def blockL2Norm (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f : MRing ι) : ℝ :=
  Real.sqrt ((1 / 2) *
    ((∫ x, (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV) +
      ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV))

end Block

def ChangeOfLattice.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    (fun n : ℕ => latLogIndex x (matAct B x) n -
        (top I (matAct B x) m' D - top I x m D) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

def ProjectionBounds.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e → IsPullFS d.x e d.m →
    ∃ (k : ℕ) (E : Fin (projDeg d.x e) → MvPolynomial (Ix κ) ℤ) (C : ℝ),
      (∀ l, (E l).IsHomogeneous k) ∧
      LinearIndependent (fnField (d.x ∘ e)) (fun l => aeval d.x (E l)) ∧
      (∀ (n : ℕ) (s : Ω) (l : Fin (projDeg d.x e)), s ∈ sec ℤ d.x n →
        secTrace d.x e (n + k) (s * aeval d.x (E l)) ∈ sec ℤ (d.x ∘ e) (n + k)) ∧
      (∀ (n : ℕ) (s : Ω), s ∈ sec ℤ d.x n →
        (∀ l, secTrace d.x e (n + k) (s * aeval d.x (E l)) = 0) → s = 0) ∧
      (∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)) ∧
      (∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ) (l : Fin (projDeg d.x e))
          (c : ℝ),
        f.IsHomogeneous n → g.IsHomogeneous (n + k) →
        aeval (d.x ∘ e) g = secTrace d.x e (n + k) (aeval d.x f * aeval d.x (E l)) →
        (∀ z ∈ pts (coordIdeal ℤ d.x), ptNorm d.m (Int.castRingHom ℂ) n f z ≤ c) →
        ∀ t : Fin (D + 1) → ℂ, t ≠ 0 →
          ptNorm (fsMetric (Fin (D + 1))) (Int.castRingHom ℂ) (n + k) g t ≤ C * c) ∧
      (∀ (n : ℕ) (Q : Fin (projDeg d.x e) → MvPolynomial (Fin (D + 1)) ℤ) (c : Fin (projDeg d.x e) → ℝ),
        k ≤ n → (∀ l, (Q l).IsHomogeneous (n - k)) →
        (∀ l, ∀ t : Fin (D + 1) → ℂ, t ≠ 0 →
          ptNorm (fsMetric (Fin (D + 1))) (Int.castRingHom ℂ) (n - k) (Q l) t ≤ c l) →
        ∀ z ∈ pts (coordIdeal ℤ d.x),
          ptNorm d.m (Int.castRingHom ℂ) n (∑ l, rename e (Q l) * E l) z ≤ C * ∑ l, c l) ∧
      (∀ n : ℕ, k + 1 ≤ n →
        (projDeg d.x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ resChi d n ∧
        resChi d n ≤ (projDeg d.x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1))

def MonomialDegree.Statement : Prop :=
  (∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Ix (Fin (D + 1)) → Ω), coordIdeal ℤ x = ⊥ →
      ∀ n, chi x (fsMetric (Ix (Fin (D + 1)))) (gaussMeasure (Ix (Fin (D + 1)))) n = chiP D n) ∧
  ∀ D : ℕ, ∃ C : ℝ, ∀ n : ℕ, 0 ≤ chiP D n ∧ chiP D n ≤ C * (n : ℝ) ^ (D + 1) ∧
    0 ≤ chiP D (n + 1) - chiP D n ∧ (1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1))

def ReductionToProjective.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ),
    I.IsFamily →
    (∀ e : Fin (D + 1) → Ix κ, IsProjFrame d.x e → IsPullFS d.x e d.m →
      (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
          (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
        =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) ∧
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D

def HilbertSamuelProjective.Statement : Prop :=
  ∀ (D : ℕ) (I : AllFam), I.IsFamily → hsDefect D (chiP D) (hhOf I D) =o[atTop] pw D

def TheoremHSM.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ),
    I.IsFamily →
    hsDefect D (resChi d) (top I d.x d.m D) =o[atTop] pw D ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionSectionL2Norm d n f

def TheoremHSMBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω),
    I.IsFamily →
    hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) =o[atTop] pw D ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f

def SlopeLowerBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ),
    I.IsFamily → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      top I d.x d.m D * n / (((D : ℝ) + 1) * genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1) - ε * n ≤
        resChi d n / (Module.finrank ℤ (sec ℤ d.x n) : ℝ)

def G1.Statement : Prop := ArithmeticIntersectionNonneg

def SuccessiveMinimaSpan.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmallGeneratedDatum P0 y D A →
    ∃ C : ℝ, ∀ n : ℕ,
      AddSubgroup.closure {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s} = chartLat y A.a n

def SuccessiveMinimaDual.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    IsConjInvariantH A → (∀ sg, 0 < Λ sg) →
    (∀ sg, Λ (NumberField.ComplexEmbedding.conjugate sg) = Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z) →
    0 ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
      ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
        ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

def G2.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι)
    (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D M →
    ∃ (k : ℕ) (e : Ω) (C : ℝ), 1 ≤ k ∧ 0 ≤ C ∧ e ≠ 0 ∧ e ∈ chartLat y ((k : ℤ) • M.a - 1) 1 ∧
      IsBoundedH (mCoordIdeal y) y (HermLine.zcomb M (fsH ι) k (-1)) 1 (Real.exp C) e ∧
      (∀ p q : ℕ, 0 < p → k * p < q →
        IsSemipositiveRel P0 (mCoordIdeal y) (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p) ∧
        IsConjInvariantH (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p) ∧
        KH.AmpleV ℚ (KH.genIdeal y) (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a ∧
        (∀ ℓ : ℕ, ℓ.Prime →
          KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a) ∧
        ∀ (n : ℕ) (s : Ω), s ∈ chartLat y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a n →
          s * e ^ (p * n) ∈ chartLat y M.a (q * n) ∧
          ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p) n c s →
            IsBoundedH (mCoordIdeal y) y M (q * n) (c * Real.exp ((p * n : ℕ) * C)) (s * e ^ (p * n))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
        |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p) /
            (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => M)| < ε ∧
        |(genDeg (mCoordIdeal y) D (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
            genDeg (mCoordIdeal y) D M.a| < ε

def G3.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M L' : HermLine ι) (P0 P0' : Ideal (MRing ι)) (II : IntersectionSystem)
    (a : ℕ) (iota : ℕ → Ω →+ Ω),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D M → IsSmallGeneratedDatum P0' y D L' → IsConjInvariantH L' → 1 ≤ a →
    (∀ n, a ∣ n → Set.InjOn (iota n) (chartLat y M.a n) ∧
      Set.MapsTo (iota n) (chartLat y M.a n) (chartLat y L'.a n)) →
    (∀ η : ℝ, 0 < η → ∃ (n₀ : ℕ) (O : Set ((Σ k, ι k) → ℂ)), IsOpen O ∧
      mcPts (mCoordIdeal y) ⊆ closure (O ∩ mcPts (mCoordIdeal y)) ∧
      ∀ n, n₀ ≤ n → a ∣ n → ∀ f ∈ chartLat y M.a n,
        PtBoundOn y M L' n (O ∩ mcPts (mCoordIdeal y)) (Real.exp (n * η)) f (iota n f)) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => L')

def ArithmeticVolumeMultiplicative.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M L : HermLine ι) (P0 P0' : Ideal (MRing ι)) (II : IntersectionSystem)
    (a : ℕ) (iota : ℕ → Ω →+ Ω) (Λ t : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D M → P0' ≤ mCoordIdeal y → IsSemipositiveRel P0' (mCoordIdeal y) L →
    IsConjInvariantH L → 0 < genDeg (mCoordIdeal y) D L.a →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ sg, 0 < Λ sg) → (∀ sg, Λ (NumberField.ComplexEmbedding.conjugate sg) = Λ sg) →
    (∀ sg, t (NumberField.ComplexEmbedding.conjugate sg) = t sg) →
    (∃ (q : ℕ) (w : Fin q → Ω), (∀ j, w j ∈ chartLat y L.a 1) ∧ KH.GeneratesOn y L.a w ∧
      ∀ j, IsBoundedHOver (mCoordIdeal y) y L 1 Λ (w j)) →
    ∑ sg, Real.log (Λ sg) ≤ ∑ sg, t sg → 1 ≤ a →
    (∀ n, a ∣ n → Set.InjOn (iota n) (chartLat y M.a n) ∧
      Set.MapsTo (iota n) (chartLat y M.a n) (chartLat y L.a n) ∧
      ∀ (θ : F) (f : Ω), iota n (algebraMap F Ω θ * f) = algebraMap F Ω θ * iota n f) →
    (∀ η : ℝ, 0 < η → ∃ (n₀ : ℕ) (O : Set ((Σ k, ι k) → ℂ)), IsOpen O ∧
      mcPts (mCoordIdeal y) ⊆ closure (O ∩ mcPts (mCoordIdeal y)) ∧
      ∀ n, n₀ ≤ n → a ∣ n → ∀ f ∈ chartLat y M.a n, ∀ sg : F →+* ℂ,
        PtBoundOn y M L n (O ∩ mcPts (mCoordIdeal y) ∩ {z | LiesOver y sg z})
          (Real.exp (n * (t sg + η))) f (iota n f)) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => L) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D L.a * ((∑ sg, t sg) / Fintype.card (F →+* ℂ))

def G4.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D M → 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => M) →
    ∃ (n : ℕ) (s : Ω), 1 ≤ n ∧ s ∈ chartLat y M.a n ∧ s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y M n c s

def G5.Statement : Prop := SuccessiveMinimaLowerBound

def G6.StatementA : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
      (m : ConeMetric ℂ (Ix κ)) (II : IntersectionSystem),
      IsIntersectionSystem II → IsGoodDatum D x m →
      top II x m D ≤
        arVolP (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x (HermLine.ofCone m))
          (chartLat (ι := GlobalTheory κ) x (HermLine.ofCone m).a) 1 D

def G6.StatementB : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D M →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤ arVolP (IsSmallH (mCoordIdeal y) y M) (chartLat y M.a) 1 D

def G6.Statement : Prop := G6.StatementA ∧ G6.StatementB

def ArithmeticVolumeBig.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

def ArithmeticVolumeResolution.Statement : Prop := HeightBoundResolution

def NefOnGenericOfSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (A : HermLine ι),
    P0 ≤ P → IsSemipositiveRel P0 P A → NefOnGeneric P A

theorem ArithmeticVolumeBig.of_moriwakiBig (hN : NefOnGenericOfSemipos.Statement) (hM : MoriwakiBigStatement) :
    ArithmeticVolumeBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 II _ hII har hb hP0 hs hnef hc
  exact hM K ι Ω y D A P0 II hII har hb hP0 hs hc hnef (hN K ι _ P0 A hP0 hs)

theorem ArithmeticVolumeBig.arithmeticVolumeBig_smoothFibre (h : ArithmeticVolumeBig.Statement) : ArithmeticVolumeLowerBound := by
  intro K _ ι _ Ω _ _ y D A II hD hII har hb _ hs hnef hc
  exact h K ι Ω y D A (mCoordIdeal y) II hD hII har hb le_rfl hs hnef hc

theorem ArithmeticVolumeBig.arithmeticVolumeBig_resolution (h : ArithmeticVolumeBig.Statement) : SuccessiveMinimaResolution := by
  intro _ _ K _ ι _ Ω _ _ y D A II hD hII har hb hs hnef hc
  exact h K ι Ω y D A (mCoordIdeal y) II hD hII har hb le_rfl hs hnef hc

theorem G6.statementB_of_G6Prime (h : ArithmeticVolumeBig.Statement) : G6.StatementB := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM
  exact h K ι Ω y D M P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos hM.nef hM.conjInv

def ArithmeticVolumeBigRefined.Statement : Prop := BirationalPullbackPushforwardFormula

def G7.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n /
        ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def ArithmeticVolumeNef.Statement : Prop := ArithmeticHilbertSamuelUpperBound

def ArithmeticVolumeNefDual.Statement : Prop := ArithmeticHilbertSamuelUpperBoundNumberField

def Lift.Statement : Prop := KH.LiftStatement

def LiftPrime.Statement : Prop := KH.LiftStatement

def IntegralClosureFinite.Statement : Prop := KH.NormalizationBoundedIndexStatement

def Perturb.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι))
    (p q : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmallGeneratedDatum P0 y D L → 1 ≤ p →
    1 ≤ q →
    IsSmallGeneratedDatum P0 y D (HermLine.zcomb L (fsH ι) q p) ∧
      KH.AmpleV ℚ (KH.genIdeal y) (HermLine.zcomb L (fsH ι) q p).a ∧
      ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (HermLine.zcomb L (fsH ι) q p).a

def LatticeWithoutBigness.Statement : Prop := SuccessiveMinimaUpperBound

namespace ProjLine

theorem mConeMap_eq_of_isMultiHomog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    mConeMap y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp only [mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem eq_zero_of_aeval_y {f : MRing (GlobalTheory (Fin 2))} {d : Unit → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f = 0 := by
  have hmem : f ∈ mCoordIdeal (ι := GlobalTheory (Fin 2)) y := by
    show mConeMap y f = 0
    rw [mConeMap_eq_of_isMultiHomog y hf, h0, map_zero, zero_mul]
  rw [mCoordIdeal_y] at hmem
  exact (Submodule.mem_bot _).mp hmem

theorem geoNum_zero_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (V : Ideal (MRing ι))
    (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs <;> positivity

theorem nefOnFibres_of_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : NefOnFibres P a := by
  intro W _ _ _ _
  rw [geoNum]
  split_ifs with h
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    exact finsum_nonneg fun W' => finsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl

theorem genDeg_y : genDeg (ι := GlobalTheory (Fin 2)) (mCoordIdeal y) 1 (fun _ => 1) = 1 := by
  unfold genDeg
  rw [mCoordIdeal_y, Ideal.map_bot]
  have h := GroundTheory.Heights₂.Heights.FieldNumbers.intNum_projectiveSpace ℚ 1
  convert h using 2 <;> first | rfl | exact Subsingleton.elim _ _ | (funext i j; rfl)

theorem isInvMat_one (J : Type) [Fintype J] [DecidableEq J] : IsInvMat (1 : Matrix J J ℚ) :=
  ⟨1, fun v => by simp⟩

theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  funext i
  simp only [matActC, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

def eP1 : Fin 2 → Ix (Fin 2) := fun k => ⟨(), k⟩

theorem coordIdeal_projectiveLine_eq_bot : coordIdeal ℤ (y ∘ eP1) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hc : coneMap ℤ (y ∘ eP1) f = coneMap ℤ y (rename eP1 f) := by
    simp only [coneMap, aeval_rename]
    rfl
  have h1 : rename eP1 f ∈ coordIdeal ℤ y := by
    show coneMap ℤ y (rename eP1 f) = 0
    rw [← hc]
    exact hf
  rw [coordIdeal_y, Ideal.mem_bot] at h1
  have hinj : Function.Injective eP1 := fun a b h => by
    simpa [eP1] using congrArg Sigma.snd h
  exact rename_injective eP1 hinj (by rw [h1, map_zero])

theorem isProjFrame_y : IsProjFrame y eP1 where
  inj a b h := by simpa [eP1] using congrArg Sigma.snd h
  free := coordIdeal_projectiveLine_eq_bot
  integral i := by
    apply isIntegral_of_mem_subalgebra
    refine ⟨X i.2, ?_⟩
    obtain ⟨⟨⟩, j⟩ := i
    simp [coneMap, eP1]

theorem isPullFS_y : IsPullFS y eP1 (fsMetric (Ix (Fin 2))) := by
  intro z _
  change ‖WithLp.toLp 2 z‖ = _
  rw [EuclideanSpace.norm_eq]
  congr 1

theorem norm_le_fs (z : Ix (Fin 2) → ℂ) (p : Ix (Fin 2)) : ‖z p‖ ≤ (fsMetric (Ix (Fin 2))).ρ z := by
  change ‖z p‖ ≤ ‖WithLp.toLp 2 z‖
  rw [EuclideanSpace.norm_eq]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun q => ‖(WithLp.toLp 2 z).ofLp q‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ p)

abbrev fsLine1 : HermLine (GlobalTheory (Fin 2)) := HermLine.ofCone (fsMetric (Ix (Fin 2)))

theorem isSmallH_coord (j : Fin 2) : IsSmallH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 (y ⟨(), j⟩) := by
  intro dg dh g h z hg hh hdeg he _
  have hdg : dg = dh + fun _ => 1 := by
    funext k
    have := hdeg k
    simp only [fsLine1, HermLine.ofCone, Pi.one_apply, Nat.cast_one, mul_one] at this
    simp only [Pi.add_apply]
    omega
  have hX : IsMultiHomog (X ⟨(), j⟩ * h : MRing (GlobalTheory (Fin 2))) dg := by
    have := mhMul (isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), j⟩) hh
    convert this using 1
    rw [hdg]
    funext k
    simp [add_comm]
  have hf : IsMultiHomog (g + -(X ⟨(), j⟩ * h)) dg := mhAdd hg (mhNeg hX)
  have h0 : aeval y (g + -(X ⟨(), j⟩ * h)) = 0 := by
    rw [map_add, map_neg, map_mul, aeval_X, he]
    ring
  have heq : g = X ⟨(), j⟩ * h := by
    have := eq_zero_of_aeval_y hf h0
    linear_combination this
  rw [heq, map_mul, map_mul, map_X, eval_X, norm_mul, pow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_fs z ⟨(), j⟩) (norm_nonneg _)

theorem coord_mem_chartLat (j : Fin 2) : y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1 := by
  change ∀ c : ∀ k, GlobalTheory (Fin 2) k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    y ⟨(), j⟩ * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * fsLine1.a k)) ∈ chartRingZ y c
  intro c _
  have : y ⟨(), j⟩ * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * fsLine1.a k)) = y ⟨(), j⟩ / y ⟨(), c ()⟩ := by
    simp [fsLine1, HermLine.ofCone, div_eq_mul_inv]
  rw [this]
  exact Algebra.subset_adjoin ⟨⟨(), j⟩, rfl⟩

theorem generatesOn_coords : KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) := by
  intro c hc
  refine ⟨fun j => if j = c () then 1 else 0, fun j => ?_, ?_⟩
  · show (if j = c () then (1 : FnField) else 0) ∈ chartRingZ y c
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Finset.sum_eq_single (c ()) (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_true, one_mul, Finset.univ_unique, Finset.prod_singleton, fsLine1, HermLine.ofCone,
      Pi.one_apply, zpow_neg, zpow_one]
    exact mul_inv_cancel₀ (hc ())

theorem genDeg_fsLine1 : genDeg (ι := GlobalTheory (Fin 2)) (mCoordIdeal y) 1 fsLine1.a = 1 := genDeg_y

theorem isSmallGeneratedDatum_fs : IsSmallGeneratedDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 where
  normalForm_baseLattice_le_dualSpan_sup_line := bot_le
  semipos := isSemipositiveRel_fs _ _
  deg_pos := by rw [genDeg_fsLine1]; exact one_pos
  gen := ⟨2, fun j => y ⟨(), j⟩, coord_mem_chartLat, generatesOn_coords, isSmallH_coord⟩

theorem isNefBigDatum_fs : IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 where
  normalForm_baseLattice_le_dualSpan_sup_line := bot_le
  semipos := isSemipositiveRel_fs _ _
  conjInv := isConjInvariantH_fs _
  nef := nefOnFibres_of_nonneg _ _ fun _ => zero_le_one
  big := by rw [genDeg_fsLine1]; exact one_pos

theorem isGoodDatum_fs : IsGoodDatum 1 y (fsMetric (Ix (Fin 2))) where
  one_le := le_rfl
  arith := isArithVar_y
  indep := linearIndependent_y
  smooth := isSmoothMetric_fs
  conjInv := isConjInvariant_fs
  semipos := ⟨⊥, bot_le, isSemipositiveRel_fs _ _⟩

theorem monomials_le_fs (z : Ix (Fin 2) → ℂ) (μ : Ix (Fin 2) →₀ ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = 1) :
    ‖∏ p, z p ^ μ p‖ ≤ 1 * fsLine1.h z := by
  have hs : μ ⟨(), 0⟩ + μ ⟨(), 1⟩ = 1 := by simpa [Fin.sum_univ_two] using hμ ()
  have hp : ∏ p, z p ^ μ p = z ⟨(), 0⟩ ^ μ ⟨(), 0⟩ * z ⟨(), 1⟩ ^ μ ⟨(), 1⟩ := by
    rw [Fintype.prod_sigma]
    simp [Fin.prod_univ_two]
  rw [hp, one_mul]
  rcases Nat.eq_zero_or_pos (μ ⟨(), 0⟩) with h0 | h0
  · have h1 : μ ⟨(), 1⟩ = 1 := by omega
    rw [h0, h1, pow_zero, pow_one, one_mul]
    exact norm_le_fs z _
  · have h0' : μ ⟨(), 0⟩ = 1 := by omega
    have h1 : μ ⟨(), 1⟩ = 0 := by omega
    rw [h0', h1, pow_zero, pow_one, mul_one]
    exact norm_le_fs z _

theorem ptBoundOn_id (n : ℕ) (U : Set (Ix (Fin 2) → ℂ)) {c : ℝ} (hc : 1 ≤ c) (f : FnField) :
    PtBoundOn (ι := GlobalTheory (Fin 2)) y fsLine1 fsLine1 n U c f f := by
  intro dg dh dg' dh' g h g' h' hg hh hdeg he hg' hh' hdeg' he' z _ hz hz'
  have hd : dg + dh' = dg' + dh := by
    funext k
    have h1 := hdeg k
    have h2 := hdeg' k
    simp only [Pi.add_apply]
    omega
  have hf : IsMultiHomog (g * h' + -(g' * h)) (dg + dh') := by
    refine mhAdd (mhMul hg hh') (mhNeg ?_)
    rw [hd]
    exact mhMul hg' hh
  have h0 : aeval y (g * h' + -(g' * h)) = 0 := by
    rw [map_add, map_neg, map_mul, map_mul, he, he']
    ring
  have hpoly : g * h' = g' * h := by
    have := eq_zero_of_aeval_y hf h0
    linear_combination this
  have hev : eval z (MvPolynomial.map (Int.castRingHom ℂ) g) * eval z (MvPolynomial.map (Int.castRingHom ℂ) h') =
      eval z (MvPolynomial.map (Int.castRingHom ℂ) g') * eval z (MvPolynomial.map (Int.castRingHom ℂ) h) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hpoly]
  have hρ0 : 0 ≤ fsLine1.h z := norm_nonneg (WithLp.toLp 2 z)
  have heqr : ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) g')‖ /
      (‖eval z (MvPolynomial.map (Int.castRingHom ℂ) h')‖ * fsLine1.h z ^ n) =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) g)‖ /
      (‖eval z (MvPolynomial.map (Int.castRingHom ℂ) h)‖ * fsLine1.h z ^ n) := by
    have hn : ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) h)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hn' : ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) h')‖ ≠ 0 := norm_ne_zero_iff.mpr hz'
    have hnorm := congrArg norm hev
    rw [norm_mul, norm_mul] at hnorm
    by_cases hr : fsLine1.h z ^ n = 0
    · simp [hr]
    · field_simp
      linarith [hnorm]
  rw [heqr]
  exact le_mul_of_one_le_left (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg hρ0 _))) hc

theorem mhZsmul (c : ℤ) {f : MRing (GlobalTheory (Fin 2))} {d : Unit → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (c • f) d :=
  fun m hm => hf m (support_smul hm)

theorem liesOver_rat (sg : ℚ →+* ℂ) (z : Ix (Fin 2) → ℂ) : LiesOver (ι := GlobalTheory (Fin 2)) y sg z := by
  intro d g h θ hg hh he
  have hf : IsMultiHomog ((θ.den : ℤ) • g + -(θ.num • h)) d :=
    mhAdd (mhZsmul _ hg) (mhNeg (mhZsmul _ hh))
  have h0 : aeval y ((θ.den : ℤ) • g + -(θ.num • h)) = 0 := by
    rw [map_add, map_neg, map_zsmul, map_zsmul, he, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc]
    have : ((θ.den : ℤ) : FnField) * algebraMap ℚ FnField θ = (θ.num : FnField) := by
      rw [← map_intCast (algebraMap ℚ FnField), ← map_mul, ← map_intCast (algebraMap ℚ FnField) θ.num]
      congr 1
      push_cast
      exact Rat.den_mul_eq_num θ
    rw [this]
    ring
  have hp := eq_zero_of_aeval_y hf h0
  have hz := congrArg (fun f => eval z (MvPolynomial.map (Int.castRingHom ℂ) f)) hp
  simp only [map_add, map_neg, map_zero, zsmul_eq_mul, map_mul, map_intCast] at hz
  rw [eq_ratCast sg θ, Rat.cast_def]
  have hden : ((θ.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast θ.den_nz
  field_simp
  push_cast at hz ⊢
  linear_combination hz

theorem existsUnique_liesOver_rat (z : Ix (Fin 2) → ℂ) :
    ∃! sg : ℚ →+* ℂ, LiesOver (ι := GlobalTheory (Fin 2)) y sg z :=
  ⟨Rat.castHom ℂ, liesOver_rat _ z, fun _ _ => Subsingleton.elim _ _⟩

def projectiveLineMultiHomogResolution : AnRes (ι := GlobalTheory (Fin 2)) (mCoordIdeal y) ProjectiveLineResolution.JJ 1 :=
  { projectiveLineAnalyticResolution with
    nondeg := by rw [← coordIdeal_eq_mCoordIdeal]; exact projectiveLineAnalyticResolution.nondeg
    mem := by rw [← coordIdeal_eq_mCoordIdeal]; exact projectiveLineAnalyticResolution.mem
    surj := by rw [← coordIdeal_eq_mCoordIdeal]; exact projectiveLineAnalyticResolution.surj }

def hsmBlockProjLine : HSMBlockDatum 1 Unit (GlobalTheory (Fin 2)) FnField where
  y := y
  k₀ := ()
  A := fsLine1
  P0 := ⊥
  J := ProjectiveLineResolution.JJ
  R := projectiveLineMultiHomogResolution
  meas := projectiveLineMeasurableSpace
  borel := projectiveLineBorel
  dV := fubiniStudyVolumeProjectiveLine
  one_le := le_rfl
  arith := isArithVar_y'
  birat := fun d g h hg hh hh0 => ⟨d (), g, h, by convert hg using 1; funext k; cases k; simp [blockDeg],
    by convert hh using 1; funext k; cases k; simp [blockDeg], hh0, rfl⟩
  deg := by funext k; simp [unitDeg, fsLine1, HermLine.ofCone]
  conjInv := isConjInvariantH_fs _
  normalForm_baseLattice_le_dualSpan_sup_line := bot_le
  semipos := isSemipositiveRel_fs _ _
  vol := isSmoothVolume_p1Vol

end ProjLine

section Inhabitants

open ProjLine

theorem ChangeOfLattice.hyps_inhabited :
    IsArithVar (ι := GlobalTheory (Fin 2)) (coordIdeal ℤ y) (1 + 1) ∧ LinearIndependent ℤ y ∧
      IsInvMat (1 : Matrix (Ix (Fin 2)) (Ix (Fin 2)) ℚ) ∧ IsSmoothMetric (fsMetric (Ix (Fin 2))) ∧
      ∀ z, (fsMetric (Ix (Fin 2))).ρ (matActC 1 z) = (fsMetric (Ix (Fin 2))).ρ z :=
  ⟨isArithVar_y, linearIndependent_y, isInvMat_one _, isSmoothMetric_fs, fun z => by rw [matActC_one]⟩

theorem ProjectionBounds.hyps_inhabited :
    ∃ d : HSMDatum 1 FnField (Fin 2), IsProjFrame d.x eP1 ∧ IsPullFS d.x eP1 d.m :=
  ⟨hsmProjLine, isProjFrame_y, isPullFS_y⟩

theorem MonomialDegree.hyps_inhabited : coordIdeal ℤ (y : Ix (Fin (1 + 1)) → FnField) = ⊥ := coordIdeal_y

theorem ReductionToProjective.hyps_inhabited :
    ∃ d : HSMDatum 1 FnField (Fin 2), IsProjFrame d.x eP1 ∧ IsPullFS d.x eP1 d.m :=
  ProjectionBounds.hyps_inhabited

theorem TheoremHSM.hyps_inhabited : Nonempty (HSMDatum 1 FnField (Fin 2)) := ⟨hsmProjLine⟩

theorem SlopeLowerBound.hyps_inhabited : Nonempty (HSMDatum 1 FnField (Fin 2)) := ⟨hsmProjLine⟩

theorem G1.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      fsLine1.a = (fun _ => ((1 : ℕ) : ℤ)) ∧ IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧
      MonomialsBounded (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 (fun _ => 1) ∧ IsConjInvariantH fsLine1 :=
  ⟨isArithVar_y', birational_y, rfl, isSemipositiveRel_fs _ _,
    fun z _ μ hμ => by simpa using monomials_le_fs z μ hμ, isConjInvariantH_fs _⟩

theorem SuccessiveMinimaDual.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      fsLine1.a = (fun _ => ((1 : ℕ) : ℤ)) ∧ IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧
      IsConjInvariantH fsLine1 ∧ (∀ _sg : ℚ →+* ℂ, (0 : ℝ) < 1) ∧
      (∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃! sg : ℚ →+* ℂ, LiesOver (ι := GlobalTheory (Fin 2)) y sg z) ∧
      ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∀ sg : ℚ →+* ℂ, LiesOver (ι := GlobalTheory (Fin 2)) y sg z →
        ∀ μ : Ix (Fin 2) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = 1) → ‖∏ p, z p ^ μ p‖ ≤ 1 * fsLine1.h z :=
  ⟨isArithVar_y', birational_y, rfl, isSemipositiveRel_fs _ _, isConjInvariantH_fs _, fun _ => one_pos,
    fun z _ => existsUnique_liesOver_rat z, fun z _ _ _ μ hμ => monomials_le_fs z μ hμ⟩

theorem G2.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 :=
  ⟨isArithVar_y', birational_y, isNefBigDatum_fs⟩

theorem G3.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 ∧ IsSmallGeneratedDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 ∧
      IsConjInvariantH fsLine1 ∧
      (∀ n, 1 ∣ n → Set.InjOn (AddMonoidHom.id FnField) (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n) ∧
        Set.MapsTo (AddMonoidHom.id FnField) (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n)
          (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n)) ∧
      ∀ η : ℝ, 0 < η → ∃ (n₀ : ℕ) (O : Set (Ix (Fin 2) → ℂ)), IsOpen O ∧
        mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) ⊆ closure (O ∩ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y)) ∧
        ∀ n, n₀ ≤ n → 1 ∣ n → ∀ f ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n,
          PtBoundOn (ι := GlobalTheory (Fin 2)) y fsLine1 fsLine1 n (O ∩ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y))
            (Real.exp (n * η)) f (AddMonoidHom.id FnField f) := by
  refine ⟨isArithVar_y', birational_y, isNefBigDatum_fs, isSmallGeneratedDatum_fs, isConjInvariantH_fs _,
    fun n _ => ⟨fun a _ b _ h => h, fun a ha => ha⟩, fun η hη => ⟨0, Set.univ, isOpen_univ, ?_, ?_⟩⟩
  · rw [Set.univ_inter]
    exact subset_closure
  · intro n _ _ f _
    exact ptBoundOn_id n _ (Real.one_le_exp (by positivity)) f

theorem ArithmeticVolumeMultiplicative.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 ∧ IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧
      IsConjInvariantH fsLine1 ∧ 0 < genDeg (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) 1 fsLine1.a ∧
      (∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃! sg : ℚ →+* ℂ, LiesOver (ι := GlobalTheory (Fin 2)) y sg z) ∧
      (∀ _sg : ℚ →+* ℂ, (0 : ℝ) < 1) ∧
      (∃ (q : ℕ) (w : Fin q → FnField), (∀ j, w j ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
        KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a w ∧
        ∀ j, IsBoundedHOver (F := ℚ) (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 (fun _ => 1) (w j)) ∧
      ∑ _sg : ℚ →+* ℂ, Real.log 1 ≤ ∑ _sg : ℚ →+* ℂ, (0 : ℝ) ∧
      (∀ n, 1 ∣ n → Set.InjOn (AddMonoidHom.id FnField) (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n) ∧
        Set.MapsTo (AddMonoidHom.id FnField) (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n)
          (chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n) ∧
        ∀ (θ : ℚ) (f : FnField), AddMonoidHom.id FnField (algebraMap ℚ FnField θ * f) =
          algebraMap ℚ FnField θ * AddMonoidHom.id FnField f) ∧
      ∀ η : ℝ, 0 < η → ∃ (n₀ : ℕ) (O : Set (Ix (Fin 2) → ℂ)), IsOpen O ∧
        mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) ⊆ closure (O ∩ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y)) ∧
        ∀ n, n₀ ≤ n → 1 ∣ n → ∀ f ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a n, ∀ sg : ℚ →+* ℂ,
          PtBoundOn (ι := GlobalTheory (Fin 2)) y fsLine1 fsLine1 n
            (O ∩ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) ∩ {z | LiesOver (ι := GlobalTheory (Fin 2)) y sg z})
            (Real.exp (n * (0 + η))) f (AddMonoidHom.id FnField f) := by
  refine ⟨isArithVar_y', birational_y, isNefBigDatum_fs, isSemipositiveRel_fs _ _, isConjInvariantH_fs _,
    by rw [genDeg_fsLine1]; exact one_pos, fun z _ => existsUnique_liesOver_rat z, fun _ => one_pos,
    ⟨2, fun j => y ⟨(), j⟩, coord_mem_chartLat, generatesOn_coords, fun j _ dg dh g h z a b c d e _ => by
      rw [one_mul]
      exact isSmallH_coord j dg dh g h z a b c d e⟩, by simp,
    fun n _ => ⟨fun a _ b _ h => h, fun a ha => ha, fun _ _ => rfl⟩,
    fun η hη => ⟨0, Set.univ, isOpen_univ, ?_, ?_⟩⟩
  · rw [Set.univ_inter]
    exact subset_closure
  · intro n _ _ f _ _
    exact ptBoundOn_id n _ (Real.one_le_exp (by positivity)) f

theorem G4.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 :=
  G2.hyps_inhabited

theorem G6.hyps_inhabited :
    IsGoodDatum 1 y (fsMetric (Ix (Fin 2))) ∧ IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧
      Birational (ι := GlobalTheory (Fin 2)) y ∧ IsNefBigDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 :=
  ⟨isGoodDatum_fs, isArithVar_y', birational_y, isNefBigDatum_fs⟩

theorem ArithmeticVolumeBig.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧
      NefOnFibres (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1.a ∧ IsConjInvariantH fsLine1 :=
  ⟨isArithVar_y', birational_y, isSemipositiveRel_fs _ _, nefOnFibres_of_nonneg _ _ fun _ => zero_le_one,
    isConjInvariantH_fs _⟩

theorem G7.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsSmallGeneratedDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 ∧ IsConjInvariantH fsLine1 :=
  ⟨isArithVar_y', birational_y, isSmallGeneratedDatum_fs, isConjInvariantH_fs _⟩

theorem Perturb.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsSmallGeneratedDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 :=
  ⟨isArithVar_y', birational_y, isSmallGeneratedDatum_fs⟩

theorem TheoremHSMBlock.hyps_inhabited : Nonempty (HSMBlockDatum 1 Unit (GlobalTheory (Fin 2)) FnField) :=
  ⟨hsmBlockProjLine⟩

theorem SuccessiveMinimaSpan.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧
      IsSmallGeneratedDatum (ι := GlobalTheory (Fin 2)) ⊥ y 1 fsLine1 :=
  ⟨isArithVar_y', birational_y, isSmallGeneratedDatum_fs⟩

theorem ArithmeticVolumeNefDual.hyps_inhabited :
    (∀ sg : ℚ →+* ℂ, (fun _ : ℚ →+* ℂ => (1 : ℝ)) (NumberField.ComplexEmbedding.conjugate sg) = 1) ∧
      ∑ _sg : ℚ →+* ℂ, Real.log 1 ≤ 0 :=
  ⟨fun _ => rfl, by simp⟩

theorem G5.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ ⊥ ≤ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) ∧ IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧
      NefOnFibres (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1.a ∧ IsConjInvariantH fsLine1 :=
  ⟨isArithVar_y', bot_le, isSemipositiveRel_fs _ _, nefOnFibres_of_nonneg _ _ fun _ => zero_le_one,
    isConjInvariantH_fs _⟩

theorem Lift.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y ∧ (0 : ℚ) < 1 ∧
      NefOnFibres (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1.a :=
  ⟨isArithVar_y', birational_y, one_pos, nefOnFibres_of_nonneg _ _ fun _ => zero_le_one⟩

theorem IntegralClosureFinite.hyps_inhabited :
    (∀ _k : Unit, 1 ≤ (fun _ => 1 : Unit → ℕ) _k) ∧ (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧
      Birational (ι := GlobalTheory (Fin 2)) y :=
  ⟨fun _ => le_rfl, fun k => ⟨0, by cases k; simp⟩, birational_y⟩

theorem ArithmeticVolumeResolution.hyps_inhabited :
    fsLine1.a = 1 ∧ IsArithVar (mCoordIdeal (fun p : Σ _ : Unit, Fin 2 => y ⟨(), p.2⟩)) (1 + 1) ∧
      Birational (fun p : Σ _ : Unit, Fin 2 => y ⟨(), p.2⟩) ∧
      IsSemipositiveH (mCoordIdeal (fun p : Σ _ : Unit, Fin 2 => y ⟨(), p.2⟩)) fsLine1 ∧ IsConjInvariantH fsLine1 :=
  ⟨by funext k; simp [fsLine1, HermLine.ofCone], isArithVar_y', birational_y, isSemipositiveRel_fs _ _,
    isConjInvariantH_fs _⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
