import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Defs

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

def dxc (r : ℕ) : Measure (Fin r → ℂ) :=
  (volume : Measure (Fin r → ℂ)).withDensity fun c => ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹)

def RTest (Ψ : RadSp k r z z' π π') : Prop :=
  ∃ K : Set ((Fin r → ℂ) × Mx k r), IsCompact K ∧ K ⊆ DomR k r z z' ∧
    ∀ x, x ∉ K → (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0

def radIp (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') : ℂ :=
  ∫ c, ∫ x : Mt k r, inner ℂ (B.hsVec ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
    (B.hsVec ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ ∂(dxc r)

def RAdj (μ : Measure (Mt k r)) (a : Pr (RadSp k r z z' π π')) : Prop :=
  (∀ Ψ, RTest Ψ → RTest (a.1 Ψ)) ∧ (∀ Ψ, RTest Ψ → RTest (a.2.unop Ψ)) ∧
    (∀ Φ Ψ, RTest Ψ → radIp μ (a.1 Φ) Ψ = radIp μ Φ (a.2.unop Ψ)) ∧
    ∀ Φ Ψ, RTest Ψ → radIp μ (a.2.unop Φ) Ψ = radIp μ Φ (a.1 Ψ)

def RadApply1 (a : Pr (RadSp k r z z' π π')) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r z z' π π' 0 (JF.Om k r z z') →
    ∀ Φ : RadSp k r z z' π π',
      (∀ x ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) J x.1 x.2) →
      ∀ x ∈ DomR k r z z',
        resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 = (a.1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def RadAdj1 (a : Pr (RadSp k r z z' π π')) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r z z' π π' 0 (JF.Om k r z z') →
    ∀ Φ : RadSp k r z z' π π',
      (∀ x ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) J x.1 x.2) →
      ∀ x ∈ DomR k r z z',
        resG k r (Fin.last r) (B.opAdj Θ J) x.1 x.2 = (a.2.unop Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def OpProp1 (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos D) Θ ∧ B.Commutes D (B.GPos D) Θ ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 ≤ d ∧ B.PolyCoef D ε d (B.opOrder Θ + 5) Θ) ∧
    ∀ F, NiceAll D F → NiceAll D (B.opApply Θ F) ∧ NiceAll D (B.opAdj Θ F)

end Defs

def RDSYReal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∃ Y : ℂ, star Y = Y ∧ Y - 1 ∈ st.inv ∧ Y ∈ st.inv ∧ Y + 1 ∈ st.inv

def RDSOpAv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y - 1 ∈ st.inv → Y ∈ st.inv → Y + 1 ∈ st.inv →
      ∃ Θ : B.DiffOp P.k P.r Wp Wq, OpProp1 D Θ ∧ RadApply1 (L.Ahatv (Y + 1)) Θ

def RDSOpR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y - 1 ∈ st.inv → Y ∈ st.inv → Y + 1 ∈ st.inv →
      ∃ Θ : B.DiffOp P.k P.r Wp Wq, OpProp1 D Θ ∧ RadApply1 (GiR L * st.xi Y * RhR L st Y) Θ

def RDSOpRv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y - 1 ∈ st.inv → Y ∈ st.inv → Y + 1 ∈ st.inv →
      ∃ Θ : B.DiffOp P.k P.r Wp Wq, OpProp1 D Θ ∧ RadApply1 (GiR L * st.xi (Y + 1) * RhvR L st (Y + 1)) Θ

def RDSOpA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y - 1 ∈ st.inv → Y ∈ st.inv → Y + 1 ∈ st.inv →
      ∃ Θ : B.DiffOp P.k P.r Wp Wq, OpProp1 D Θ ∧ RadApply1 (L.Ahat Y) Θ

def RDSIpLin : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ →
    (∀ Φ₁ Φ₂ Ψ : RadSp k r z z' π π', RTest Ψ → radIp μ (Φ₁ + Φ₂) Ψ = radIp μ Φ₁ Ψ + radIp μ Φ₂ Ψ) ∧
    (∀ Φ Ψ₁ Ψ₂ : RadSp k r z z' π π', RTest Ψ₁ → RTest Ψ₂ →
      radIp μ Φ (Ψ₁ + Ψ₂) = radIp μ Φ Ψ₁ + radIp μ Φ Ψ₂) ∧
    ∀ (w : ℂ) (Φ Ψ : RadSp k r z z' π π'),
      radIp μ (w • Φ) Ψ = starRingEnd ℂ w * radIp μ Φ Ψ ∧ radIp μ Φ (w • Ψ) = w * radIp μ Φ Ψ

def RDSCoordAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ l, RAdj μ (L.p l) ∧ RAdj μ (L.pb l) ∧ RAdj μ (L.c l) ∧ RAdj μ (L.ci l) ∧ RAdj μ (L.cb l) ∧ RAdj μ (L.cbi l)

def RDSFnAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    RAdj μ L.GGi

def RDSQQAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ (Y : ℂ) (a b : Fin 2), RAdj μ (st.QQ Y a b)

def RDSXiTest : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → ∀ Ψ : RadSp P.k P.r z z' π π', RTest Ψ →
      RTest ((st.xi Y).1 Ψ) ∧ RTest ((st.xi Y).2.unop Ψ)

def RDSFund : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Φ₁ Φ₂ : RadSp P.k P.r z z' π π', (∀ Ψ, RTest Ψ → radIp μ Φ₁ Ψ = radIp μ Φ₂ Ψ) →
      ∀ x ∈ DomR P.k P.r z z', (Φ₁ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2

def RDSSection : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Ψ : RadSp P.k P.r z z' π π', RTest Ψ →
      ∃ K : B.Mat P.k P.r → (Wq →L[ℂ] Wp), K ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') ∧
        (∀ x ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (K) x.1 x.2)

def RDSPair : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Θ : B.DiffOp P.k P.r Wp Wq, OpProp1 D Θ →
    ∀ J K : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      K ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
    ∀ Φ₁ Φ₂ Φ₃ Φ₄ : RadSp P.k P.r z z' π π',
      (∀ x ∈ DomR P.k P.r z z', (Φ₁ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.opAdj Θ J) x.1 x.2) →
      (∀ x ∈ DomR P.k P.r z z', (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (K) x.1 x.2) →
      (∀ x ∈ DomR P.k P.r z z', (Φ₃ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (J) x.1 x.2) →
      (∀ x ∈ DomR P.k P.r z z', (Φ₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.opApply Θ K) x.1 x.2) →
      RTest Φ₂ → radIp μ Φ₁ Φ₂ = radIp μ Φ₃ Φ₄

section Closure

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem rds_fst_mul (a b : Pr V) : (a * b).1 = a.1 * b.1 := rfl
theorem rds_snd_mul (a b : Pr V) : (a * b).2.unop = b.2.unop * a.2.unop := rfl
theorem rds_fst_add (a b : Pr V) : (a + b).1 = a.1 + b.1 := rfl
theorem rds_snd_add (a b : Pr V) : (a + b).2.unop = a.2.unop + b.2.unop := rfl
theorem rds_fst_alg (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
theorem rds_snd_alg (w : ℂ) :
    (algebraMap ℂ (Pr V) w).2.unop = algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ w) := rfl

end Closure

section Sub

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rTest_add {Ψ₁ Ψ₂ : RadSp k r z z' π π'} (h₁ : RTest Ψ₁) (h₂ : RTest Ψ₂) : RTest (Ψ₁ + Ψ₂) := by
  obtain ⟨K₁, hK₁, hD₁, h0₁⟩ := h₁
  obtain ⟨K₂, hK₂, hD₂, h0₂⟩ := h₂
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, Set.union_subset hD₁ hD₂, fun x hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  simp [h0₁ x hx.1, h0₂ x hx.2]

theorem rTest_smul (w : ℂ) {Ψ : RadSp k r z z' π π'} (h : RTest Ψ) : RTest (w • Ψ) := by
  obtain ⟨K, hK, hD, h0⟩ := h
  exact ⟨K, hK, hD, fun x hx => by simp [h0 x hx]⟩

def IpLinAt (μ : Measure (Mt k r)) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (π' : Mx k r → (Wq →L[ℂ] Wq)) : Prop :=
  (∀ Φ₁ Φ₂ Ψ : RadSp k r z z' π π', RTest Ψ → radIp μ (Φ₁ + Φ₂) Ψ = radIp μ Φ₁ Ψ + radIp μ Φ₂ Ψ) ∧
    (∀ Φ Ψ₁ Ψ₂ : RadSp k r z z' π π', RTest Ψ₁ → RTest Ψ₂ →
      radIp μ Φ (Ψ₁ + Ψ₂) = radIp μ Φ Ψ₁ + radIp μ Φ Ψ₂) ∧
    ∀ (w : ℂ) (Φ Ψ : RadSp k r z z' π π'),
      radIp μ (w • Φ) Ψ = starRingEnd ℂ w * radIp μ Φ Ψ ∧ radIp μ Φ (w • Ψ) = w * radIp μ Φ Ψ

variable {μ : Measure (Mt k r)}

theorem rAdj_mul {a b : Pr (RadSp k r z z' π π')} (ha : RAdj μ a) (hb : RAdj μ b) : RAdj μ (a * b) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · rw [rds_fst_mul, Module.End.mul_apply]; exact ha1 _ (hb1 _ hΨ)
  · rw [rds_snd_mul, Module.End.mul_apply]; exact hb2 _ (ha2 _ hΨ)
  · rw [rds_fst_mul, Module.End.mul_apply, ha3 _ _ hΨ, hb3 _ _ (ha2 _ hΨ), rds_snd_mul, Module.End.mul_apply]
  · rw [rds_snd_mul, Module.End.mul_apply, hb4 _ _ hΨ, ha4 _ _ (hb1 _ hΨ), rds_fst_mul, Module.End.mul_apply]

theorem rAdj_add (hL : IpLinAt μ z z' π π') {a b : Pr (RadSp k r z z' π π')} (ha : RAdj μ a) (hb : RAdj μ b) :
    RAdj μ (a + b) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · rw [rds_fst_add, LinearMap.add_apply]; exact rTest_add (ha1 _ hΨ) (hb1 _ hΨ)
  · rw [rds_snd_add, LinearMap.add_apply]; exact rTest_add (ha2 _ hΨ) (hb2 _ hΨ)
  · rw [rds_fst_add, LinearMap.add_apply, hL.1 _ _ _ hΨ, ha3 _ _ hΨ, hb3 _ _ hΨ, rds_snd_add, LinearMap.add_apply,
      hL.2.1 _ _ _ (ha2 _ hΨ) (hb2 _ hΨ)]
  · rw [rds_snd_add, LinearMap.add_apply, hL.1 _ _ _ hΨ, ha4 _ _ hΨ, hb4 _ _ hΨ, rds_fst_add, LinearMap.add_apply,
      hL.2.1 _ _ _ (ha1 _ hΨ) (hb1 _ hΨ)]

theorem rAdj_alg (hL : IpLinAt μ z z' π π') (w : ℂ) : RAdj μ (algebraMap ℂ (Pr (RadSp k r z z' π π')) w) := by
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · rw [rds_fst_alg, Module.algebraMap_end_apply]; exact rTest_smul _ hΨ
  · rw [rds_snd_alg, Module.algebraMap_end_apply]; exact rTest_smul _ hΨ
  · rw [rds_fst_alg, rds_snd_alg, Module.algebraMap_end_apply, Module.algebraMap_end_apply, (hL.2.2 _ _ _).1,
      (hL.2.2 _ _ _).2]
  · rw [rds_fst_alg, rds_snd_alg, Module.algebraMap_end_apply, Module.algebraMap_end_apply, (hL.2.2 _ _ _).1,
      (hL.2.2 _ _ _).2, Complex.conj_conj]

def rAdjSub (hL : IpLinAt μ z z' π π') : Subalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | RAdj μ a}
  mul_mem' := rAdj_mul
  add_mem' := rAdj_add hL
  algebraMap_mem' := rAdj_alg hL
  one_mem' := by have h := rAdj_alg hL 1; rwa [map_one] at h
  zero_mem' := by have h := rAdj_alg hL 0; rwa [map_zero] at h

theorem rAdj_inv {x xi : Pr (RadSp k r z z' π π')} (hx : RAdj μ x) (h1 : x * xi = 1) (h2 : xi * x = 1)
    (ht : ∀ Ψ, RTest Ψ → RTest (xi.1 Ψ) ∧ RTest (xi.2.unop Ψ)) : RAdj μ xi := by
  obtain ⟨-, -, hx3, hx4⟩ := hx
  have e1 : ∀ Φ, x.1 (xi.1 Φ) = Φ := fun Φ => by
    have := congrArg (fun p : Pr (RadSp k r z z' π π') => p.1 Φ) h1
    simpa [rds_fst_mul] using this
  have e2 : ∀ Φ, x.2.unop (xi.2.unop Φ) = Φ := fun Φ => by
    have := congrArg (fun p : Pr (RadSp k r z z' π π') => p.2.unop Φ) h2
    simpa [rds_snd_mul] using this
  refine ⟨fun Ψ hΨ => (ht Ψ hΨ).1, fun Ψ hΨ => (ht Ψ hΨ).2, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · conv_lhs => rw [← e2 Ψ]
    rw [← hx3 _ _ (ht Ψ hΨ).2, e1]
  · conv_lhs => rw [← e1 Ψ]
    rw [← hx4 _ _ (ht Ψ hΨ).1, e2]

end Sub

section Mem

variable {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A)

theorem rds_mat_mul_mem {M N : Matrix (Fin 2) (Fin 2) A} (hM : ∀ i j, M i j ∈ S) (hN : ∀ i j, N i j ∈ S) :
    ∀ i j, (M * N) i j ∈ S := fun i j => by
  rw [Matrix.mul_apply]; exact S.sum_mem fun l _ => S.mul_mem (hM i l) (hN l j)

theorem rds_mat_prod_mem (l : List (Matrix (Fin 2) (Fin 2) A)) (h : ∀ M ∈ l, ∀ i j, M i j ∈ S) :
    ∀ i j, l.prod i j ∈ S := by
  induction l with
  | nil => intro i j; rw [List.prod_nil, Matrix.one_apply]; split_ifs; exacts [S.one_mem, S.zero_mem]
  | cons M l ih =>
    rw [List.prod_cons]
    exact rds_mat_mul_mem S (h M List.mem_cons_self) (ih fun N hN => h N (List.mem_cons_of_mem _ hN))

theorem matrix_fin_two_entries_mem {M : Matrix (Fin 2) (Fin 2) A} (h00 : M 0 0 ∈ S) (h01 : M 0 1 ∈ S) (h10 : M 1 0 ∈ S)
    (h11 : M 1 1 ∈ S) : ∀ i j, M i j ∈ S := by
  intro i j; fin_cases i <;> fin_cases j <;> assumption

variable {r : ℕ} (L : R.LevelData A r)

theorem rds_Tprod_mem (hp : ∀ l, L.p l ∈ S) (hc : ∀ l, L.c l ∈ S) (hci : ∀ l, L.ci l ∈ S) (Y : ℂ) :
    ∀ i j, L.Tprod Y i j ∈ S := by
  refine rds_mat_prod_mem S _ fun M hM => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hM)
  exact matrix_fin_two_entries_mem S (S.add_mem (S.algebraMap_mem Y) (hp l)) (S.neg_mem (hc l)) (hci l) S.zero_mem

theorem rds_Tvprod_mem (hp : ∀ l, L.pb l ∈ S) (hc : ∀ l, L.cb l ∈ S) (hci : ∀ l, L.cbi l ∈ S) (Y : ℂ) :
    ∀ i j, L.Tvprod Y i j ∈ S := by
  refine rds_mat_prod_mem S _ fun M hM => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hM)
  exact matrix_fin_two_entries_mem S (S.sub_mem (S.algebraMap_mem Y) (hp l)) (S.neg_mem (hc l)) (hci l) S.zero_mem

theorem rds_ofFn_prod_mem (f : Fin r → A) (h : ∀ l, f l ∈ S) : (List.ofFn f).prod ∈ S :=
  list_prod_mem fun x hx => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact h l

end Mem

theorem rAdj_thR (hLin : RDSIpLin) (hC : RDSCoordAdj) (hF : RDSFnAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → Y + 1 ∈ st.inv → ∀ j, RAdj μ (thR L st Y j) := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hY hY1
  have hL : IpLinAt μ z z' π π' := hLin P.k P.r z z' Wp Wq π π' μ hD.2.1
  let S := rAdjSub hL
  have hc := hC Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  have hp : ∀ l, L.p l ∈ S := fun l => (hc l).1
  have hpb : ∀ l, L.pb l ∈ S := fun l => (hc l).2.1
  have hcc : ∀ l, L.c l ∈ S := fun l => (hc l).2.2.1
  have hci : ∀ l, L.ci l ∈ S := fun l => (hc l).2.2.2.1
  have hcb : ∀ l, L.cb l ∈ S := fun l => (hc l).2.2.2.2.1
  have hcbi : ∀ l, L.cbi l ∈ S := fun l => (hc l).2.2.2.2.2
  have hG : L.GGi ∈ S := hF Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  have hq : ∀ Y a b, st.QQ Y a b ∈ S := hQ Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  have hLS : Fr.IsLevelStart L st := hD.2.2.2.2.2.2.2
  have hx : ∀ Y, st.x Y ∈ S := fun Y => by
    have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hLS.tau Y, ← mul_assoc, L.GGi_GG, one_mul]
    rw [e]; exact S.mul_mem hG (hq Y 1 1)
  have hxi : ∀ Y, star Y = Y → Y ∈ st.inv → st.xi Y ∈ S := fun Y hs hi =>
    rAdj_inv (hx Y) (hLS.x_xi Y hi).1 (hLS.x_xi Y hi).2
      (hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hs hi)
  have hT := rds_Tprod_mem S L hp hcc hci
  have hTv := rds_Tvprod_mem S L hpb hcb hcbi
  have hDr : L.Dr ∈ S := rds_ofFn_prod_mem S _ hcc
  have hDrb : L.Drb ∈ S := rds_ofFn_prod_mem S _ hcb
  have hGi : GiR L ∈ S :=
    S.mul_mem (S.mul_mem (rds_ofFn_prod_mem S _ hci) (rds_ofFn_prod_mem S _ hcbi)) hG
  have hR : ∀ Y, RhR L st Y ∈ S := fun Y =>
    S.mul_mem hDrb (S.add_mem (S.mul_mem (hq Y 1 0) (hT Y 0 0)) (S.mul_mem (hq Y 1 1) (hT Y 1 0)))
  have hRv : ∀ Y, RhvR L st Y ∈ S := fun Y =>
    S.mul_mem hDr (S.add_mem (S.mul_mem (hq Y 0 1) (hTv Y 0 0)) (S.mul_mem (hq Y 1 1) (hTv Y 1 0)))
  have hYs1 : star (Y + 1) = Y + 1 := by rw [star_add, hYs, star_one]
  intro j
  fin_cases j
  · exact S.mul_mem hDrb (hTv (Y + 1) 0 0)
  · exact S.mul_mem (S.mul_mem hGi (hxi Y hYs hY)) (hR Y)
  · exact S.mul_mem (S.mul_mem hGi (hxi (Y + 1) hYs1 hY1)) (hRv (Y + 1))
  · exact S.mul_mem hDr (hT Y 0 0)

theorem rds_adj_of_apply (hFd : RDSFund) (hS : RDSSection) (hP : RDSPair) (hRes : RDResRad) (hFF : RDOpFF) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ (Θ : B.DiffOp P.k P.r Wp Wq) (a : Pr (RadSp P.k P.r z z' π π')), OpProp1 D Θ → RAdj μ a → RadApply1 a Θ →
      RadAdj1 a Θ := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Θ a hO ha hA
  subst hz hz' hπ hπ'
  intro J hJ Φ hΦ x hx
  have hJ' : B.opAdj Θ J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (JF.Om P.k P.r D.z D.z') :=
    (hFF P.k P.r Wp Wq D Θ hO.1 hO.2.1 J hJ).2
  obtain ⟨Φ', hΦ'⟩ := hRes Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD (B.opAdj Θ J) hJ'
  have heq := hFd Wp Wq P D.z D.z' D.π D.π' X μ L st l0 D hD hl1 hl2 rfl rfl rfl rfl hr Φ' (a.2.unop Φ)
    (fun Ψ hΨ => by
      obtain ⟨K, hK, hKΨ⟩ := hS Wp Wq P D.z D.z' D.π D.π' X μ L st l0 D hD hl1 hl2 rfl rfl rfl rfl hr Ψ hΨ
      have h4 : ∀ y ∈ DomR P.k P.r D.z D.z',
          ((a.1 Ψ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
            resG P.k P.r (Fin.last P.r) (B.opApply Θ K) y.1 y.2 := fun y hy => (hA K hK Ψ hKΨ y hy).symm
      rw [hP Wp Wq P D.z D.z' D.π D.π' X μ L st l0 D hD hl1 hl2 rfl rfl rfl rfl hr Θ hO J K hJ hK Φ' Ψ Φ (a.1 Ψ)
        hΦ' hKΨ hΦ h4 hΨ, ha.2.2.2 Φ Ψ hΨ])
  rw [← hΦ' x hx]
  exact heq x hx

theorem rDIdentSpec_of_cut (hY : RDSYReal) (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hLin : RDSIpLin) (hC : RDSCoordAdj) (hF : RDSFnAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hFd : RDSFund)
    (hS : RDSSection) (hP : RDSPair) (hRes : RDResRad) (hFF : RDOpFF) : RDIdentSpec := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨Y, hYs, hYm, hYi, hY1⟩ := hY Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨Θ0, o0, a0⟩ := h0 Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hYm hYi hY1
  obtain ⟨Θ1, o1, a1⟩ := h1 Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hYm hYi hY1
  obtain ⟨Θ2, o2, a2⟩ := h2 Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hYm hYi hY1
  obtain ⟨Θ3, o3, a3⟩ := h3 Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hYm hYi hY1
  have hO : ∀ j, OpProp1 D (![Θ0, Θ1, Θ2, Θ3] j) := by
    intro j; fin_cases j
    exacts [o0, o1, o2, o3]
  have hAp : ∀ j, RadApply1 (thR L st Y j) (![Θ0, Θ1, Θ2, Θ3] j) := by
    intro j; fin_cases j
    exacts [a0, a1, a2, a3]
  have hAd := rAdj_thR hLin hC hF hQ hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYs hYi hY1
  refine ⟨Y, ![Θ0, Θ1, Θ2, Θ3], hYs, hYi, hY1, hO, ?_⟩
  intro j J hJ Φ hΦ x hx
  exact ⟨hAp j J hJ Φ hΦ x hx, rds_adj_of_apply hFd hS hP hRes hFF Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz'
    hπ hπ' hr _ _ (hO j) (hAd j) (hAp j) J hJ Φ hΦ x hx⟩

end Formalism.FourierDecayAlt.P.CutSE
