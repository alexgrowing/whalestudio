import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.KComm

variable {D : D7}

theorem comm_of_unitary_isom {m : ℕ} {u J : Matrix (Fin m) (Fin m) ℂ} (hu : uᴴ * u = 1) (hJ : uᴴ * J * u = J) :
    u * J = J * u := by
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.1 hu
  calc u * J = u * (uᴴ * J * u) := by rw [hJ]
    _ = (u * uᴴ) * J * u := by simp only [Matrix.mul_assoc]
    _ = J * u := by rw [hu', Matrix.one_mul]

theorem compAt_K_comm (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    compAt θ τ (mat k) * blk4 0 1 (-1) 0 = blk4 0 1 (-1) 0 * compAt θ τ (mat k) := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (AdelicU.archEquiv (Jst D n) (isCMExt_host D) (embOverOf D τ)
    (AdelicU.projArch D.sp.cm.sig (Jst D n) (placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (embOverOf D τ).1 := by
    rw [e1, e2, AdelicU.infMat_infProj (Jst D n) (isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  exact comm_of_unitary_isom hunit hiso'

end GlobalTheory.StdUnn.KComm

namespace GlobalTheory.StdUnn.KComm

theorem exists_stdInv_comm_K : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D A μ hμ κ hκ θ hθ
  obtain ⟨k₀, -, hk₀⟩ := GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hch : ∀ g τ, (Tm A μ).map (tauE D τ) * compAt θ τ (mat (κ g)) =
      compAt θ τ (Formalism.L2.Theta.mt (dblSp A) g) * (Tm A μ).map (tauE D τ) := by
    intro g τ
    have h2 := congrArg (compAt θ τ) (hκ g)
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, hr] at h2
    exact h2
  refine ⟨fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)), fun τ => ?_, fun k hk τ => ?_⟩
  · have h := hch (κ.symm k₀) τ
    rw [κ.apply_symm_apply, hk₀] at h
    exact h.symm
  · dsimp only
    set T := (Tm A μ).map (tauE D τ) with hTdef
    have hT : IsUnit T.det := by
      have h := (GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ).2.1.map (tauE D τ)
      rwa [RingHom.map_det] at h
    set X := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)
    set S := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))
    set U := compAt θ τ (mat (κ k))
    have hX : T * U = X * T := hch k τ
    have hS : T * stdInv A.rank μ τ = S * T := by
      have h := hch (κ.symm k₀) τ
      rw [κ.apply_symm_apply, hk₀] at h
      exact h
    have hU : U * stdInv A.rank μ τ = stdInv A.rank μ τ * U := by
      rw [stdInv, Matrix.mul_smul, Matrix.smul_mul, compAt_K_comm θ hθ A.rank (κ k) hk τ]
    have key : X * S * T = S * X * T := by
      calc X * S * T = X * (T * stdInv A.rank μ τ) := by rw [hS, Matrix.mul_assoc]
        _ = T * U * stdInv A.rank μ τ := by rw [hX, Matrix.mul_assoc]
        _ = T * stdInv A.rank μ τ * U := by rw [Matrix.mul_assoc, hU, Matrix.mul_assoc]
        _ = S * X * T := by rw [hS, Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have h2 := congrArg (· * T⁻¹) key
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] using h2

end GlobalTheory.StdUnn.KComm

end
