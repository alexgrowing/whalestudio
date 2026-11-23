import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataTheta

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open Formalism.MainNotions.S

noncomputable section

namespace Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def lam48 (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun i => if h : i.val < k - 1 then v ⟨i.val, h⟩
    else -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def InterlacingCondition (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ h : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩

def HalfIntegralDifference (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ i s, ∃ j : ℤ, u i - lam48 k r v b s = (j : ℝ) + 1 / 2

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def GapC (C : ℝ) (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
    C * (rk48 k r : ℝ) ^ 3 < b ⟨j.val + 1, hj⟩ - b j

def LowGapGe (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j

def RealPlaceNumericalSetting (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ∧ InterlacingCondition k r u v b ∧
    HalfIntegralDifference k r u v b ∧ GapBig k r b

def wtF (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (X km : Mat k r) : ℝ :=
  ∏ i : Fin (2 * r + k),
    (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^
      (-(lam48 k r v b ⟨i.val, by omega⟩ - lam48 k r v b ⟨i.val + 1, by omega⟩ + 1))

def rank1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : H →L[ℂ] H :=
  (innerSL ℂ x).smulRight x

def embUk (k : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j =>
    if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def Conclusion1 (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC C k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def HasOrdLe (k r : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type*} [NormedAddCommGroup Wp]
    (N : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w v‖).sum

def FunctionalContinuityOrder (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC C k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ HasOrdLe k r (rk48 k r ^ 2 / 2 + 1) σ B ∧
    ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def Conclusion2 (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC C k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp,
    AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    IsSPsiEquiv z (psiGen k r z c) π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), rconv μG (eFun μG σ w) W x = W x

def TParity {D : Formalism.BasicNotions.D7} (P : Formalism.BasicNotions.TH.TPar D) : Prop :=
  ∀ τ, (∀ i, ∃ n : ℤ, P.u τ i = (n : ℚ) + 1 / 2) ∧ (∀ i, ∃ n : ℤ, P.v τ i = (n : ℚ)) ∧
    (∀ j, ∃ n : ℤ, P.b τ j = (n : ℚ)) ∧ ∀ j, ∃ n : ℤ, P.e τ j = (n : ℚ)

def NCGaps {D : Formalism.BasicNotions.D7} (P : Formalism.BasicNotions.TH.TPar D) : Prop :=
  ∀ j : ℕ, j ≤ D.R.m → ∀ τ, ∀ x ∈ P.Dpar j τ, ∀ y ∈ P.Dpar j τ, x.2 ≠ y.2 →
    ((D.R.r + D.R.m * P.t : ℕ) : ℚ) ^ 3 < |x.1 - y.1|

def car {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (μ : ℕ → X.Chr) (s i : ℕ) : X.Chr :=
  if Even i then μ s * X.etaT⁻¹ else μ s

def Hyp3 {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (P : Formalism.BasicNotions.TH.TPar D) : Prop :=
  1801 ≤ D.R.r + P.t ∧ P.Interlace ∧ TParity P ∧ P.Centred ∧ NCGaps P ∧ ∀ τ, P.eta τ = -X.infTy X.etaT τ

def IsMu {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (P : Formalism.BasicNotions.TH.TPar D) (μ : ℕ → X.Chr) : Prop :=
  ∀ (j : Fin D.R.m) τ, X.infTy (μ (j.1 + 1)) τ = -P.e τ j

def IsDv {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (P : Formalism.BasicNotions.TH.TPar D) (j : ℕ)
    (F : X.AF (X.Ys P.t j)) : Prop :=
  X.conjAF _ F ∈ X.typ _ (P.Dpar j)

def vth {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (t : ℕ) (μ : ℕ → X.Chr) (j : ℕ)
    (Φ : X.Sch (X.Ys t (j + 1)) (X.Ys t j)) : X.cusp (X.Ys t (j + 1)) →ₗ[ℂ] X.AF (X.Ys t j) :=
  X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ

def bB {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (t j : ℕ) (pos : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (φ : X.AF (X.Xs t j)) (F : X.cusp (X.Ys t j)) : ℂ :=
  X.Bj t j pos s (X.conjAF _ φ) F

def IsAutRep {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (V : Formalism.BasicNotions.TH.HSp D) (π : Submodule ℂ (X.AF V)) : Prop :=
  X.IsStable V π ∧ π ≠ ⊥ ∧ ∀ π' : Submodule ℂ (X.AF V), π' ≤ π → X.IsStable V π' → π' = ⊥ ∨ π' = π

def PointsLemma (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P →
  ∃ (μ : ℕ → X.Chr) (π : Submodule ℂ (X.AF (X.Xs P.t 0))) (φ : X.AF (X.Xs P.t 0))
    (F : ∀ j : ℕ, X.cusp (X.Ys P.t j)) (Φ : ∀ j : ℕ, X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j))
    (pos : X.Pos (X.Xs P.t 0) (X.Ys P.t 0) (X.iXYs P.t 0)),
    IsMu X P μ ∧ IsAutRep X _ π ∧ π ≤ X.typeX P 0 ∧ φ ∈ π ∧
    IsDv X P D.R.m (F D.R.m : X.AF (X.Ys P.t D.R.m)) ∧
    (∀ j : ℕ, j < D.R.m → Φ j ∈ X.fact _ _ ∧ Φ j ∈ X.kfin _ _ ∧
      ((F j : X.cusp (X.Ys P.t j)) : X.AF (X.Ys P.t j)) = vth X P.t μ j (Φ j) (F (j + 1)) ∧
      IsDv X P j (F j : X.AF (X.Ys P.t j))) ∧
    bB X P.t 0 pos 0 φ (F 0) ≠ 0

def PerNZ {D : Formalism.BasicNotions.D7} (X : Formalism.BasicNotions.ThetaX D) (t j : ℕ) (φ : X.AF (X.Xs t j)) (F : X.cusp (X.Ys t j)) : Prop :=
  (j < D.R.m ∧ ∃ pos s, bB X t j pos s φ F ≠ 0) ∨
    ∃ h : j = D.R.m, X.Btop (X.Xs t j) (X.Ys t j) (h ▸ X.iYXm t) (X.conjAF _ φ) F ≠ 0

def RallisSiegelWeilFormula (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P →
  ∃ (μ : ℕ → X.Chr) (π : ∀ j : ℕ, Submodule ℂ (X.AF (X.Xs P.t j))), IsMu X P μ ∧
    (∀ j, j ≤ D.R.m → IsAutRep X _ (π j) ∧ π j ≤ X.cusp _ ∧ π j ≤ X.typeX P j) ∧
    ∀ j, j < D.R.m → ∀ φ ∈ π (j + 1),
      ∃ (N : ℕ) (Φ' : Fin N → X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))) (φ' : Fin N → X.cusp (X.Xs P.t j)),
        (∀ a, Φ' a ∈ X.fact _ _ ∧ Φ' a ∈ X.kfin _ _ ∧ (φ' a : X.AF (X.Xs P.t j)) ∈ π j) ∧
        φ = ∑ a, X.th _ _ (μ (j + 1)) (μ (j + 1)) (Φ' a) (φ' a)

def LiftParameterConditions (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P →
  ∀ π : Submodule ℂ (X.AF (X.Xs P.t D.R.m)), IsAutRep X _ π → π ≤ X.typeX P D.R.m →
  ∃ φ ∈ π, ∃ F : X.cusp (X.Ys P.t D.R.m), IsDv X P D.R.m (F : X.AF (X.Ys P.t D.R.m)) ∧ PerNZ X P.t D.R.m φ F

def ThetaUnfoldingFreeData (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j < D.R.m →
  ∀ (φ' : X.cusp (X.Xs P.t j)) (Φ' : X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))), Φ' ∈ X.fact _ _ →
    Φ' ∈ X.kfin _ _ → (φ' : X.AF (X.Xs P.t j)) ∈ X.typeX P j →
  ∀ F : X.cusp (X.Ys P.t (j + 1)), IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
    PerNZ X P.t (j + 1) (X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ') F →
  ∃ Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j), Φ ∈ X.fact _ _ ∧ Φ ∈ X.kfin _ _ ∧
    ∀ G : X.cusp (X.Ys P.t j), (G : X.AF (X.Ys P.t j)) = vth X P.t μ j Φ F → PerNZ X P.t j (φ' : X.AF (X.Xs P.t j)) G

def ThetaStablePeriodVanishing (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j < D.R.m →
  ∀ π : Submodule ℂ (X.AF (X.Ys P.t (j + 1))), X.IsStable _ π → π ≤ X.cusp _ →
    (∀ i, 1 ≤ i → i ≤ (Formalism.BasicNotions.sigYD D.R j).2 → ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.YsLow P.t j i))
      (F : X.cusp (X.Ys P.t (j + 1))), (F : X.AF (X.Ys P.t (j + 1))) ∈ π →
      X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ F = 0) →
    ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j)) (F : X.cusp (X.Ys P.t (j + 1))),
      (F : X.AF (X.Ys P.t (j + 1))) ∈ π → vth X P.t μ j Φ F ∈ X.cusp (X.Ys P.t j)

def RealThetaLiftDiscreteSeries (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ →
  (∀ j, j < D.R.m → ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j)) (F : X.cusp (X.Ys P.t (j + 1))), Φ ∈ X.kfin _ _ →
    IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) → vth X P.t μ j Φ F ∈ X.cusp (X.Ys P.t j) →
    IsDv X P j (vth X P.t μ j Φ F)) ∧
  (∀ j, j < D.R.m → ∀ i, 1 ≤ i → i ≤ (Formalism.BasicNotions.sigYD D.R j).2 →
    ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.YsLow P.t j i)) (F : X.cusp (X.Ys P.t (j + 1))),
    IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
    X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ F = 0)

def RealConstantNonvanishing (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ (P : Formalism.BasicNotions.TH.TPar D) (j : ℕ), j ≤ D.R.m →
    (∀ g F, IsDv X P j F → IsDv X P j (X.actF _ g F)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D (X.Ys P.t j) τ), ∀ F, IsDv X P j F → IsDv X P j (X.actR _ τ h F)

def AdmS (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  RallisSiegelWeilFormula D X ∧ LiftParameterConditions D X ∧ ThetaUnfoldingFreeData D X ∧ ThetaStablePeriodVanishing D X ∧ RealThetaLiftDiscreteSeries D X ∧ RealConstantNonvanishing D X

def TowerRallisLemma (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop := AdmS D X → PointsLemma D X

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
  ∀ P : Mat k r, IsCayleyU k r (eps48 k r) P →
    IsDS (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) →
  ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P))) →
  ∀ w : H, IsHighestUnit (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) w →
  ∀ X : Mat k r, Formalism.REAL.inP (eps48 k r) X →
    (E ∘L σ (P⁻¹ * NormedSpace.exp X * P) ∘L E =
      ((Module.finrank ℂ (lowKSub (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P))) : ℕ) : ℂ) •
        ∫ kk : Formalism.REAL.KG (eps48 k r),
          ((wtF k r v b X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (P⁻¹ * Formalism.REAL.toMK kk * P) w)
          ∂(Formalism.REAL.muK (eps48 k r))) ∧
    (E ∘L σ (P⁻¹ * NormedSpace.exp X * P) ∘L E).IsPositive

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
  ∀ P : Mat k r, IsCayleyU k r (eps48 k r) P →
    IsDS (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) →
  ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P))) →
  ∀ X : Mat k r, Formalism.REAL.inP (eps48 k r) X →
  ∀ h : ℝ, LowGapGe h r b →
    ‖E ∘L σ (P⁻¹ * NormedSpace.exp X * P) ∘L E‖ ≤
      Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * ((r : ℝ) + 1))))

def adm3 (_D : Formalism.BasicNotions.D7) (c0 : ℝ) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
  ∀ P : Mat k r, IsCayleyU k r (eps48 k r) P →
    IsDS (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) →
  ∀ x x' : H, IsKFin (eps48 k r) (fun g => σ (P⁻¹ * g * P)) x →
    IsKFin (eps48 k r) (fun g => σ (P⁻¹ * g * P)) x' →
  ∀ ws ws' : List (Mat k r), (∀ X ∈ ws, Formalism.REAL.inG (eps48 k r) X) → (∀ X ∈ ws', Formalism.REAL.inG (eps48 k r) X) →
  ∀ h : ℝ, LowGapGe h r b →
  ∃ Cf : ℝ, ∀ g : Mat k r, Formalism.REAL.inUJ (eps48 k r) g →
    ‖ldWord ws' (rdWord ws (fun y => ⟪x', σ (P⁻¹ * y * P) x⟫_ℂ)) g‖ ≤
      Cf * Real.sqrt (Formalism.REAL.hs g) ^ (-(c0 * h / Real.sqrt (2 * (r : ℝ) + 2)))

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
  ∀ P : Mat k r, IsCayleyU k r (eps48 k r) P →
    IsDS (eps48 k r) (lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) →
    (∀ (μ : Fin (2 * r + k + 1) → ℝ) (S : Submodule ℂ H),
      IsKTypeOf (eps48 k r) (fun g => σ (P⁻¹ * g * P)) μ S →
      ∃ cc : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℕ,
        (∀ a a', cc a a' ≠ 0 → a < a') ∧
        μ = Formalism.QuantumDeterminants.lowK (eps48 k r) (lam48 k r v b) + ∑ a, ∑ a', (cc a a' : ℝ) • Formalism.REAL.root a a') ∧
    ∀ S S' : Submodule ℂ H,
      IsKTypeOf (eps48 k r) (fun g => σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (eps48 k r) (lam48 k r v b)) S →
      IsKTypeOf (eps48 k r) (fun g => σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (eps48 k r) (lam48 k r v b)) S' →
      S = S'

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
  ∀ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ B B' : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z (psiGen k r z c) σ π B' →
    ∃ a : ℂ, (∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = a • B' x) ∨
      (∀ x ∈ smoothVecs (k := k) (r := r) σ, B' x = a • B x)

def adm6 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d

def adm7 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k : ℕ) (a : Fin (k + 1) → ℝ) (Vq : Type) [NormedAddCommGroup Vq] [InnerProductSpace ℂ Vq]
    [FiniteDimensional ℂ Vq] (π : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (Vq →L[ℂ] Vq)),
    IsHCTypeU (k + 1) a π →
    (∀ bb : Fin k → ℝ,
      (∃ S : Submodule ℂ Vq, IsKTypeOf (allPos k) (fun h => π (embUk k h)) (Formalism.QuantumDeterminants.lowK (allPos k) bb) S) ↔
        (Formalism.QuantumDeterminants.IsHCParam bb ∧ ∀ i : Fin k, bb i < a i.castSucc ∧ a i.succ < bb i)) ∧
    ∀ (bb : Fin k → ℝ) (S S' : Submodule ℂ Vq),
      IsKTypeOf (allPos k) (fun h => π (embUk k h)) (Formalism.QuantumDeterminants.lowK (allPos k) bb) S →
      IsKTypeOf (allPos k) (fun h => π (embUk k h)) (Formalism.QuantumDeterminants.lowK (allPos k) bb) S' → S = S'

def adm8 (_D : Formalism.BasicNotions.D7) : Prop :=
  Formalism.QuantumDeterminants.CapelliHW ∧ Formalism.QuantumDeterminants.CapCentral ∧ Formalism.QuantumDeterminants.QMinorLeft ∧ Formalism.QuantumDeterminants.CapLeft ∧
    Formalism.QuantumDeterminants.CapHW ∧ Formalism.QuantumDeterminants.CapComatrix

def adm9 (_D : Formalism.BasicNotions.D7) : Prop :=
  Formalism.REAL.CCR ∧ Formalism.REAL.FockPairGl ∧ Formalism.REAL.FockAdj ∧ Formalism.REAL.FockCas

def adm10 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)), IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∀ x : H, IsSmoothVec (k := k) (r := r) σ x →
  ∃ (N : ℕ) (fs : Fin N → Mat k r → ℂ) (xs : Fin N → H),
    (∀ i, Formalism.QuantumDeterminants.SmoothOnH (Formalism.QuantumDeterminants.Hpk k r) (fs i) ∧
      ∃ Kc : Set (Mat k r), IsCompact Kc ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), g ∉ Kc → fs i g = 0) ∧
    (∀ i, IsSmoothVec (k := k) (r := r) σ (xs i)) ∧
    x = ∑ i, ∫ y, fs i (Matrix.of y) • σ (Matrix.of y) (xs i) ∂μG

def admitted (D : Formalism.BasicNotions.D7) (c0 : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D c0 ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D ∧ adm9 D ∧ adm10 D

def Stmt (D : Formalism.BasicNotions.D7) (C c0 : ℝ) : Prop := admitted D c0 → Conclusion1 D C ∧ Conclusion2 D C

def HodgeTateFromSandwich (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := FunctionalContinuityOrder D C → adm2 D → adm6 D → Conclusion2 D C

def ClosedFormProjectorBound : Prop := ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ D : Formalism.BasicNotions.D7, HodgeTateFromSandwich D C

def UniformExportStatement : Prop :=
  ∀ c0 : ℝ, 0 < c0 → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ D : Formalism.BasicNotions.D7, Stmt D C c0

def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm1 (Fm.D x i)

def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm2 (Fm.D x i)

def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (c0 : ℝ) : Prop :=
  0 < c0 ∧ ∀ (x : ℝ) (i : Fm.Ix x), adm3 (Fm.D x i) c0

def admF4 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)

def admF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm5 (Fm.D x i)

def admF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm6 (Fm.D x i)

def admF7 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm7 (Fm.D x i)

def admF8 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm8 (Fm.D x i)

def admF9 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm9 (Fm.D x i)

def FamilyRowsCountHypothesis {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), adm10 (Fm.D x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (c0 : ℝ) : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm c0 ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm ∧ admF8 Fm ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm

def ConclusionF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ (x : ℝ) (i : Fm.Ix x), Conclusion1 (Fm.D x i) C

def FamilyFunctionalOrder {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ (x : ℝ) (i : Fm.Ix x), FunctionalContinuityOrder (Fm.D x i) C

def ConclusionF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ (x : ℝ) (i : Fm.Ix x), Conclusion2 (Fm.D x i) C

def ConclusionF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.ex x hx i).th

def AdmSF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), AdmS (Fm.D x i) (Fm.ex x hx i).th

def FlatLineDegreeFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmSF Fm → ConclusionF3 Fm

def DeterminantValueFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  FamilyFunctionalOrder Fm C → admF2 Fm → admF6 Fm → ConclusionF2 Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C c0 : ℝ) : Prop := AdmF Fm c0 → ConclusionF1 Fm C ∧ ConclusionF2 Fm C

def FamilyStatementAtConstants {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C c0 : ℝ) : Prop := KudlaFamilyStatement Fm C c0

end Formalism.MainNotions.CayleySignature
