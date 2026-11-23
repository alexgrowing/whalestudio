import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem

noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem crd_map_mulVec (m : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (m y) = (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i) *ᵥ X.crd y := by
  unfold Formalism.L2.SG.Pf.toV HidaSetting.crd crdOf
  have hb : ∀ j : Fin X.B.I.n, (∑ i, X.ιE ((Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) i) • X.bas i) = X.bas j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_apply, hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hb]
  funext i
  conv_lhs => rw [← X.bas.sum_repr y]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phiV_linMat (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V) :
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  obtain ⟨-, hQ, -⟩ := C.isT τ
  refine ⟨C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ *
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *
      X.B.I.P (vOf X τ) * C.Q τ, fun y => ?_⟩
  have hP : (X.B.I.P (vOf X τ))⁻¹ * ((Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) * (X.B.I.P (vOf X τ) * (X.B.I.P (vOf X τ))⁻¹)) =
      (X.B.I.P (vOf X τ))⁻¹ * (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) := by
    by_cases h : IsUnit (X.B.I.P (vOf X τ)).det
    · rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul, Matrix.zero_mul]
  have hw : (fun i => X.B.I.φ (vOf X τ) (X.crd (m y) i)) =
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *ᵥ
        (fun i => X.B.I.φ (vOf X τ) (X.crd y i)) := by
    rw [crd_map_mulVec m y]
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e1 : ∀ z, GlobalTheory.TypeAsm.phiV C τ z =
      (C.Qi τ * (X.B.I.P (vOf X τ))⁻¹) *ᵥ (fun i => X.B.I.φ (vOf X τ) (X.crd z i)) := by
    intro z
    unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.HidaSetting.rv
    rw [Matrix.mulVec_mulVec]
  rw [e1, e1, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, hP]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

theorem phiV_linMat_all : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau)
    (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  intro D X C τ m
  exact GramPf.phiV_linMat C τ m

end GlobalTheory.TypeAsm
