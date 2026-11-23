import Formalism.LocalToGlobal.GlobalTheory.GL6.PRUpLoc
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem upn_isTr_inv (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (s : (D.mem u).C.Y i) :
    IsTr (atInf (embT D) γ.1.1)
      ((Tf.val i hi).eY ((Tf.val i hi).eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).inv_mem γ.2) ((Tf.val i hi).eY s))))
      ((Tf.val i hi).eY s) := by
  intro τ
  rw [Equiv.apply_symm_apply]
  show ((Tf.val i hi).eY s).1 τ = atInf (embT D) (γ.1 : Matrix _ _ D.host.E) τ *
    (atInf (embT D) ((γ.1⁻¹ : GL _ D.host.E) : Matrix _ _ D.host.E) τ * ((Tf.val i hi).eY s).1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem upNat_of_tied (Tf : FormsTied D u) : UpNat Tf := by
  intro i hi v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := Tf.upN i hi v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun h => ?_⟩
  funext s
  rw [h6 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl

set_option maxHeartbeats 4000000 in

theorem dnNat_of_tied (Tf : FormsTied D u) : DnNat Tf := by
  intro i hi v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := Tf.dnN i hi v c g hg0
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun h => ?_⟩
  funext s
  rw [h5 h s _ (upn_isTr_inv Tf i hi γ s), Units.val_inv_eq_inv_val]
  rfl

theorem rnd_roundUp_ofM (Tf : FormsTied D u) (hL : RUpLocM Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u :=
  rnd_roundUpN Tf (upNat_of_tied Tf) (dnNat_of_tied Tf) hL

theorem rnd_roundDn_ofM (Tf : FormsTied D u) (hL : RDnLocM Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u :=
  rnd_roundDnN Tf (upNat_of_tied Tf) (dnNat_of_tied Tf) hL

theorem rnd_linkAdmT_ofM
    (h : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → RUpLocM Tf ∧ RDnLocM Tf) :
    LinkAdmT :=
  rnd_linkAdmT_ofN fun D u Tf hc =>
    ⟨upNat_of_tied Tf, dnNat_of_tied Tf, (h D u Tf hc).1, (h D u Tf hc).2, splitAtT_of_tied Tf.atT⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
