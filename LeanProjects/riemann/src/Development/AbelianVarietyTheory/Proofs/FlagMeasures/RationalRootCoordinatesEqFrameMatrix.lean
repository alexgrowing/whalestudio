import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.LoopVol

open Formalism.L2.SG.HidaSetting

theorem hJ_sum_right' {n m : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) (g : Fin m → ℂ)
    (y : Fin m → Fin n → ℂ) : hJ ε x (∑ i, g i • y i) = ∑ i, g i * hJ ε x (y i) := by
  unfold hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem ratCoord_eq_matOn : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ))) (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ)) M → ∀ q : GlobalTheory.LoopV.roots (ptMat w), GlobalTheory.LoopVol.ratCoord X u' w γ s y τ q = M q.1.1 q.1.2 := by
  intro D X u' w γ s y τ M hM q
  unfold GlobalTheory.LoopVol.ratCoord
  rw [hM q.1.2, hJ_sum_right', Fin.sum_univ_castSucc]
  have hfe : ∀ i : Fin D.R.rS, hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.castSucc i)) = if i = ⟨q.1.1.1, root_fst_lt w q⟩ then 1 else 0 := by
    intro i
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_castSucc, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans
      (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  have hfz : hJ (X.B.I.ε (X.pl.symm τ)) (rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
      (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) (Fin.last _)) = 0 := by
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one, one_smul]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X _ _ _).trans (by rw [(X.zu_orth u' _).2]; simp)
  simp only [hfe, hfz, mul_ite, mul_one, mul_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1

end GlobalTheory.LoopVol
