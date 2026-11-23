import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hermitian_module_dual_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bwd j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).2 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  exact dual_beta_reference_congruence j a

theorem mem_module_of_congruences {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hbd : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) v))
    (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) : v ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  rw [show v = (v - repr0 X v) + repr0 X v by abel]
  refine add_mem (mL_Mo X.B.I hd) ?_
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine sum_mem fun a _ => ?_
    have : hA X.B.I (X.f0 a) v • X.e0 a = (⟨_, hA_int X.B.I (hF a) hv⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hbd l) (hB l))
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

theorem hA_bwd_K (δ : X.B.I.Gf) (k j : Fin D.R.k) : hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j) = 0 := by
  rw [X.bwd_w k, X.bwd_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA]
  have := X.ew_orth
  linear_combination (hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j)) * this

variable {X} (TR : TypedRed X)
include TR

theorem adTriv_inv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) :
    Formalism.L2.SG.Pf.AdTriv X δ⁻¹ := by
  have gδ := good_of_ncong X hK hN
  have h1 : levi TR δ = 1 := (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR gδ).2 hT
  refine (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR (good_inv X gδ)).1 ?_
  rw [levi_inv TR gδ, h1, inv_one]

theorem adTriv_bwd {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) (j : Fin D.R.k) :
    (X.B.I.fmat δ - 1) *ᵥ X.bwd j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hNi := ncong_inv X hK hN
  have hTi := adTriv_inv TR hK hN hT
  have hadj : ∀ y : VA X.B.I, hA X.B.I y ((X.B.I.fmat δ - 1) *ᵥ X.bwd j) =
      hA X.B.I ((X.B.I.fmat δ⁻¹ - 1) *ᵥ y) (X.bwd j) := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_adj, Matrix.sub_mulVec, Matrix.one_mulVec,
      hA_sub_left]
  refine mem_module_of_congruences X (K_sub_mv X.B.I hK (hBd j)) (fun a => ?_) ?_ (fun l => ?_) (fun l => ?_)
  · rw [hadj]
    exact hermitian_module_dual_beta_congruence X (Mo_mono X.B.I (Set.image_subset_range _ _) (hNi.1 a)) j
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X hNi.2 j
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_bwd_K, hA_bwd_bwd, sub_zero]
    exact Z_zero X.B.I X.B.g
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X (hTi l) j

theorem adFull_of_adTriv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ)
    {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w)) :
    (X.B.I.fmat δ - 1) *ᵥ w ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hw
  have hsm : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (m : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      m ∈ Mo X.B.I X.B.g (Set.range X.e0) → c • m ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c m hc hm => by
    have : c • m = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • m := rfl
    rw [this]; exact Submodule.smul_mem _ _ hm
  rw [show w = (w - repr0 X w) + repr0 X w by abel, Matrix.mulVec_add]
  refine add_mem (mL_Mo X.B.I ?_) ?_
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mem_mL_of_Kset X hK _ hd) hd
  unfold repr0
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, mulVec_fsum X, Matrix.mulVec_smul]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => hsm _ _ (hA_int X.B.I (hF a) hw)
      (Mo_mono X.B.I (Set.image_subset_range _ _) (hN.1 a))
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (K_sub_mv X.B.I hK (hF a)))
  · exact hsm _ _ (hA_int X.B.I hZ hw) hN.2
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hBd l) hw) (hT l)
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hB l) hw) (adTriv_bwd TR hK hN hT l)

end Formalism.L2.SG.Pf.BridgeAd
