import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def wl (A B : ℂ) : ℂ →L[ℝ] ℂ := A • ContinuousLinearMap.id ℝ ℂ + B • Complex.conjCLE.toContinuousLinearMap

theorem wl_apply (A B h : ℂ) : wl A B h = A * h + B * conj h := rfl

section Slice

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wOp (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) : Module.End ℂ (RadSp k r z z' π π') :=
  (js.map (X.op l)).prod

def dT (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 2 * X.op l 0

def dTb (X : ActualOps k r z z' π π') (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') := X.op l 5 * X.op l 3

def SlDom (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π') : Prop :=
  ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
    ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
      ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c'

def SliceGood (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : RadSp k r z z' π π') : Prop :=
  Φ ∈ lcSub k r z z' π π' ∧ ∀ js : List (Fin 6), SlDom μ l c (wOp X l js Φ)

end Slice

def PairAtDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (Φ Ψ : RadSp k r z z' π π'), Φ ∈ lcSub k r z z' π π' → Ψ ∈ lcSub k r z z' π π' →
    ∀ c ∈ OmX r, ∀ (c' : Cf r l.succ) (t : ℂ), t ≠ 0 →
      HasFDerivAt (fun s => pairAt μ Φ Ψ (glue l.succ (Function.update c l s) c'))
        (wl (pairAt μ (dT X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dTb X l Ψ) (glue l.succ (Function.update c l t) c'))
            (pairAt μ (dTb X l Φ) Ψ (glue l.succ (Function.update c l t) c') +
              pairAt μ Φ (dT X l Ψ) (glue l.succ (Function.update c l t) c'))) t

def OuterLeib : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r (Fin.last r)) μ → ∀ (l : Fin r), ∀ (S : Type) [Fintype S] [DecidableEq S] (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ), c ∈ OmX r →
    (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) → ∀ t : ℂ, t ≠ 0 →
      HasFDerivAt (fun s => form μ l.succ u v (Function.update c l s))
        (wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
            (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
              form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) t

def JSliceGen : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJ P z z' π π' D l Ψ → SliceGood X μ l c Ψ

end Formalism.FourierDecayAlt.P.CutSE
