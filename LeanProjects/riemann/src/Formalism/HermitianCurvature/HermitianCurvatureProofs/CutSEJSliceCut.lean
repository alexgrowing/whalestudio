import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wlv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : E) : ℂ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight A + Complex.conjCLE.toContinuousLinearMap.smulRight B

section WaveJc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJc (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    HasCompactSupport G ∧ ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJc : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJc P z z' π π' D l Ψ}

end WaveJc

def JSliceGenC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → SliceGood X μ l c Ψ

def JSPointDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (g : Mx k r) (t : ℂ), t ≠ 0 →
    HasFDerivAt (fun s : ℂ => (Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l s) g)
      (wlv (((dT X l Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l t) g)
        (((dTb X l Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) (Function.update p l t) g)) t

def JSSob2 : Prop :=
  ∀ (t0 : ℂ) (δ : ℝ), 0 < δ → ∃ K : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f fx fy fxy : ℂ → E),
    (∀ t ∈ Metric.closedBall t0 (2 * δ),
      HasFDerivAt f (Complex.reCLM.smulRight (fx t) + Complex.imCLM.smulRight (fy t)) t) →
    (∀ t ∈ Metric.closedBall t0 (2 * δ), ∃ fyy : E,
      HasFDerivAt fy (Complex.reCLM.smulRight (fxy t) + Complex.imCLM.smulRight fyy) t) →
    ContinuousOn fx (Metric.closedBall t0 (2 * δ)) → ContinuousOn fxy (Metric.closedBall t0 (2 * δ)) →
    ∀ t ∈ Metric.ball t0 δ, ‖f t‖ ^ 2 ≤
      K * ∫ s in Metric.closedBall t0 (2 * δ), (‖f s‖ ^ 2 + ‖fx s‖ ^ 2 + ‖fy s‖ ^ 2 + ‖fxy s‖ ^ 2)

def JSPairCont : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (Φ Ψ : RadSp k r z z' π π'), Φ ∈ lcSub k r z z' π π' →
    Ψ ∈ lcSub k r z z' π π' → ContinuousOn (fun p => pairAt μ Φ Ψ p) (OmX r)

def JSMeas : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (c : Fin r → ℂ)
    (Φ Ψ : RadSp k r z z' π π'),
    Measurable (fun q : (ℂ × Cf r l.succ) × Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)))

def SpectralL2Locality : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → ∀ (js : List (Fin 6)) (t0 : ℂ),
      t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
        LevelSquareIntegrable μ l.succ (wOp X l js Ψ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ M

def JSWordNF : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π')), multiplicationOperator Wv (fun c _ => fsv s (c l)) →
    ∀ js : List (Fin 6), ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
      (∀ i, ContinuousOn (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
      ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
        (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
          ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

def JSRadLoc : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    HasCompactSupport G → ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ js : List (Fin 6), (∀ j ∈ js, j = 0 ∨ j = 3) → ∀ t0 : ℂ, t0 ≠ 0 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
        LevelSquareIntegrable μ l.succ (wOp X l js Φ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Φ) (wOp X l js Φ) c t‖ ≤ M

end Formalism.FourierDecayAlt.P.CutSE
