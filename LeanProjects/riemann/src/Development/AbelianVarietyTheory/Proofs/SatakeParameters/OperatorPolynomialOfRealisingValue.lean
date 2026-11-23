import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePolyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominatorStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem trDY_smul {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (D : D7)
    {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (r : ℂ) :
    trDY X Kc j D e Φ₀ (r • R) = ι r • trDY X Kc j D e Φ₀ R := by
  unfold trDY
  rw [Finset.smul_sum, Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, LinearMap.map_smulₛₗ, MvPolynomial.smul_monomial]
  · intro α _ h
    rw [MvPolynomial.notMem_support_iff.1 h, map_zero, MvPolynomial.monomial_zero]

theorem polDY_smul (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (r : ℂ) :
    polDY D s (r • Q) (N' := N') = r • polDY D s Q (N' := N') := by
  unfold polDY
  exact map_smul _ r Q

theorem polDel_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, MvPolynomial.coeff n (polDel X Kc j G) = ι (r * cOp X D pos j s) • MvPolynomial.coeff n (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ r Gc G hR hG s hs
  have hQr : r • Q ∈ WtPol ℂ ν := Submodule.smul_mem _ r hQ
  have hop := GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG s hs
  refine ⟨⟨_, hop⟩, GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG, fun n => ?_⟩
  rw [polDel_eq X Kc j G _ hop, polDY_smul, trDY_smul, Formalism.L2.G.Pend.cD, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul, ← Algebra.smul_def, MvPolynomial.coeff_smul, smul_smul, map_mul, mul_comm]

end GlobalTheory.TwV.DelA
