import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StContinuousRootHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter
open scoped Topology

theorem hasDerivAt_eval_cons {k : ℕ} (y : Fin k → ℂ) (P : MvPolynomial (Fin (k + 1)) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) P)
      (eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 P)) s := by
  apply P.induction_on (fun a => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simpa using hasDerivAt_const s a
  · simp only [map_add]
    exact hp.add hq
  · cases i using Fin.cases with
    | zero =>
      have h0 := hp.mul (hasDerivAt_id s)
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X 0)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * id s := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X 0)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * id s +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 1 := by
        simp [Derivation.leibniz]; ring
      rw [e1, e2]; exact h0
    | succ j =>
      have h0 := hp.mul (hasDerivAt_const s (y j))
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X j.succ)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * y j := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X j.succ)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * y j +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 0 := by
        simp [Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero j)]; ring
      rw [e1, e2]; exact h0

theorem ContinuousRootHolomorphic.proof : ContinuousRootHolomorphic.Statement := by
  intro k Q O h hO hh hQ y hy hd
  set c := eval (Fin.cons (h y) y : Fin (k + 1) → ℂ) (pderiv 0 Q) with hc
  let f : (Fin k → ℂ) × ℂ → ℂ := fun v => eval (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) Q
  have hfa : AnalyticAt ℂ f (y, h y) := by
    have hi : ∀ i : Fin (k + 1),
        AnalyticAt ℂ (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) i) (y, h y) := by
      intro i
      cases i using Fin.cases with
      | zero => simpa using analyticAt_snd
      | succ j =>
        have e : (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) j.succ) =
            ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) j).comp
              (ContinuousLinearMap.fst ℂ (Fin k → ℂ) ℂ)) := by
          funext v; simp
        rw [e]; exact ContinuousLinearMap.analyticAt _ _
    simpa [f, MvPolynomial.coe_aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hi Q
  have hf := hfa.hasStrictFDerivAt
  have hderiv : HasDerivAt (fun s => f (y, s)) c (h y) := hasDerivAt_eval_cons y Q (h y)
  have hcomp : HasFDerivAt (fun s => f (y, s))
      (fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ) (h y) :=
    hf.hasFDerivAt.comp (h y) (hasFDerivAt_prodMk_right y (h y))
  set D := fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ with hDdef
  have hD1 : D 1 = c := by
    rw [hcomp.unique hderiv.hasFDerivAt]; simp
  have hDx : ∀ x : ℂ, D x = x * c := fun x => by
    rw [← hD1, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hinv : D.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℂ ℂ) ?_ ?_ <;>
      refine ContinuousLinearMap.ext_ring ?_ <;> simp [hDx, hd]
  have hφ := hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hev := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  refine hφ.differentiableAt.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun t => (t, h t)) (𝓝 y) (𝓝 (y, h y)) :=
    (continuousAt_id.prodMk (hh.continuousAt (hO.mem_nhds hy))).tendsto
  filter_upwards [ht.eventually hev, hO.mem_nhds hy] with t ht1 ht2
  exact (ht1.mp (by simp only [f]; rw [hQ t ht2, hQ y hy])).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
