import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameScalarOddPositionsDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvenFrameBlockScalingHomogeneousPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitutionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  intro p _ X D pos Kc _ _ _ ι ρ hPT fd c hc j hN La' M hU hFr ν hν P hP
  obtain ⟨-, -, hsz', hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j (rkT X D hN) (extNu (D.R.N (j + 1)) ν) hle P hP
  have hRR : phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P = R0 := GlobalTheory.T.linearChoice_eq_realisingPolynomial X D pos (j + 1) (rkT X D hN) _ P R0 hR0
  have hdeg := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos (j + 1) (rkT X D hN) (wT X D pos j) (extNu _ ν) P R0 hP hR0
  have hphi : phi0 X D pos ι j P = MvPolynomial.map ι R0 := by
    unfold phi0
    rw [dif_pos (rkT X D hN)]
    show MvPolynomial.map ι (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P) = _
    rw [hRR]
  have hhom : ∀ m ∈ (MvPolynomial.map ι R0).support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 →
      (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) =
        (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = szT X D pos j τ := by
    intro m hm τ ho
    rw [hdeg m (MvPolynomial.support_map_subset _ _ hm) τ, if_neg ho, (GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2, if_neg ho, ← hsz' τ]
    ring
  rw [hphi, hRR]
  unfold GlobalTheory.FrameB.tauV
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt X D pos Kc fd c j La' (fun τ => szT X D pos j τ) _ hhom,
    GlobalTheory.T.latticeTupleFrame_scalar_oddPositions_det X D pos Kc ι ρ hPT fd c hc j hN La' M hU hFr ν hν, GlobalTheory.T.complex_block_action_inv_read_as_substitution X D pos Kc ι ρ hPT fd j hN La' M hU hFr R0, smul_smul, smul_smul]
  congr 1
  have hε : ∀ τ, ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ≠ 0 := fun τ =>
    (((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map ((ι.comp (embT D τ)))).ne_zero
  have hsum : c ^ (∑ τ, szT X D pos j τ) = ∏ τ, c ^ szT X D pos j τ := by
    classical
    induction (Finset.univ : Finset D.what₂.Tau) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hc, ih]
  rw [hsum, mul_assoc, ← map_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_zpow₀, map_zpow₀]
  split_ifs with ho
  · rw [mul_one, ← zpow_add₀ (hε τ)]
    ring_nf
  · rw [one_mul, ← zpow_add₀ (hε τ)]
    simp
