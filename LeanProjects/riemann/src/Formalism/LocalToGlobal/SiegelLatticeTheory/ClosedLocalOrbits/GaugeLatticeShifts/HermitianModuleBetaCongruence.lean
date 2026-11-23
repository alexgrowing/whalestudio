import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PhaseAtPf

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section GoodNC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ncong_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : NCong X x⁻¹ := by
  refine ⟨inv_e X.B.I X.B.g X.e0 hx hn.1, ?_⟩
  rw [inv_id]
  refine neg_mem (pres X.B.I (K_inv X.B.I hx) X.B.g _ _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ hn.2)
  rintro _ ⟨b, rfl⟩
  exact Mo_mono X.B.I (Set.image_subset_range _ _) (inv_e X.B.I X.B.g X.e0 hx hn.1 b)

theorem hermitian_module_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bw j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).1 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1

theorem par_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) (hni : NCong X x⁻¹) : Par X x := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat x *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x - 1) *ᵥ X.e0 a by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hn.1 a))
  · refine mem_Mo_eb X (K_mv X.B.I hx (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj]
      refine hermitian_module_beta_congruence X ?_ j
      rw [show X.B.I.fmat x⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
      exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hni.1 a))
    · rw [hA_adj, show X.B.I.fmat x⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.z0 by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (hermitian_module_beta_congruence X hni.2 j)
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem good_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : Good X x := by
  have hni := ncong_inv X hx hn
  have hxi : x⁻¹ ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
    simpa using inv_mem hx
  exact ⟨par_of_ncong X hx hn hni, par_of_ncong X hxi hni (by simpa using hn)⟩

end GoodNC

section AdmParPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def TermK : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt ∈ X.B.I.Kset

theorem adm_parity_of_norm (hK : TermK F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') : AdmPar F0 F0' cs cs' := by
  intro t
  exact good_of_ncong _ (hK t) (hN t)

end AdmParPf

end Formalism.L2.SG.NormCut
