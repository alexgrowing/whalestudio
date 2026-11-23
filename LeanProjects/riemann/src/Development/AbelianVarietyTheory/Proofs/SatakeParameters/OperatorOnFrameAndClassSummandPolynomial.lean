import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem polD_eq_map_polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D s Q y' =
      MvPolynomial.map (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q) := by
  set v : GL3Theta.FrV D N' → ℂ := fun k => y' k.1 k.2.1 k.2.2
  have hmap : ∀ P : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ),
      MvPolynomial.map (MvPolynomial.eval v) P = MvPolynomial.mapAlgHom (MvPolynomial.aeval v) P := fun P => rfl
  rw [hmap]
  unfold GL3Theta.polD polDY
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun k => ?_
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.mapAlgHom_apply]
  split_ifs with h
  · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_mul]
    simp [v]
  · simp

theorem applyFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame := by
  intro D N N' s Q G y'
  rw [polD_eq_map_polDY]
  unfold GL3Theta.applyAt0 framePol GL3Theta.evFr
  rw [map_sum]
  symm
  rw [← Finset.sum_subset (MvPolynomial.support_map_subset
    (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q))]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.eval_C, mul_assoc]
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff] at hα
    rw [MvPolynomial.coeff_map] at hα
    rw [map_mul, hα, zero_mul]

theorem entQFrame : Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ i c Q c' y'
  unfold Formalism.L2.KerInert.SecondKernelDifference.entQ
  rw [applyFrame]
  rfl

theorem applyFrame_and_entQFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame :=
  ⟨applyFrame, entQFrame⟩

end GlobalTheory.TwV.DelA
