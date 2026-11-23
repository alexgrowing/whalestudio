import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeBasisCoordinateEqCoordinateEquStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeEqComapStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLatticeEqComapBlockwiseLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerProdOrthogonalBlocksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerComapLinearIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBasisThetaEqF0FormStatement

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

theorem inter_congr_al {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α α' : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V)
    (F : V → ℂ) (h : ∀ x ∈ Λ₂, α x = α' x) : inter H α Λ₁ Λ₂ F = inter H α' Λ₁ Λ₂ F := by
  funext z
  unfold inter
  congr 1
  exact finsum_congr fun c => by rw [h _ (Quotient.out c : Λ₂).2]

theorem thetaVectorUpToUnits_thZero_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' →
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  intro D cc δ B _ _ hcc hδ _ N N' hN hN'
  obtain ⟨n, hn⟩ := hN
  obtain ⟨n', hn'⟩ := hN'
  obtain rfl : N = n * 2 := by omega
  obtain rfl : N' = n' * 2 := by omega
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  refine ⟨bas B n n', B.kappa ^ (n' * n), GlobalTheory.T.orthonormalBasis_blockVacuumLatticeBasisFamily D cc δ B n n', GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll D cc δ B _, ?_⟩
  funext z
  obtain ⟨hsc', hF0', hidx', hprod⟩ := GlobalTheory.T.latticeIntertwiner_prod_orthogonal_blocks B.L B.ω₀ B.cq (Fin n' × Fin n) (Fin 4 × D.what₂.Tau)
    (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) hS.betaSemi
    (product_theta_mem B.L B.ω₀ _ hS.per hS.half _ hS.betaStd).1.2 hS.idx₁
  have hH : IsHerm (stdH B.L (Ix D n n')) := (standardFormBasic B.L _).2.1
  have hnat := GlobalTheory.T.latticeIntertwiner_comap_linear_isometry _ _ (formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau (n * 2) (n' * 2))
    (stdH B.L (Ix D n n')) (phi B n n') (fun x y => GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x y) hH _ _ _ _ hsc' hF0' hidx' z
  rw [GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels D cc δ B hS n n' z]
  congr 1
  rw [Iop_eq, GlobalTheory.T.blockVacuumLattice_eq_comap_standardLattice, GlobalTheory.T.la_tor0_stdL_eq_blkLat, show StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.tor0 D cc δ).abelian₂ (B.ω₀ / 2))
      = fun v => F0 B.L B.ω₀ (Ix D n n') (phi B n n' v) from funext (GlobalTheory.T.pullback_basis_theta_eq_F0_form D cc δ B n n')]
  rw [inter_congr_al _ _ (fun v => alphaQ B.cq (stdH B.L (Ix D n n')) (phi B n n' v)) _ _ _ ?_, hnat, hprod]
  · rfl
  · intro x hx
    have hx' : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) := by
      rw [GlobalTheory.T.la_tor0_stdL_eq_blkLat D cc δ B n n']; exact hx
    obtain ⟨m, hm⟩ := B.qInt0 hS (n * 2) (n' * 2) x hx'
    rw [al_eq D _ x m hm]
    unfold alphaQ qOf
    rw [← GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x x]
    rfl

end GlobalTheory.BaseVacuum
