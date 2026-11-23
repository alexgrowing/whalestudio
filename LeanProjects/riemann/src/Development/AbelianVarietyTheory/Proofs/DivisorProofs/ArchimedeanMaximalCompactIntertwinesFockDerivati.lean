import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquiv

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KInfComm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
  have hB := hP.base
  have hw := hP.weil
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hk1 : k ∈ UAt σ W (evI F) := hk.1
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw ((1 : UA σ X.J)⁻¹, k⁻¹)
    (GlobalTheory.RealConjFac.inv_mem_UAt h1) (GlobalTheory.RealConjFac.inv_mem_UAt hk1)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (A f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hA f) (hT₂ (A f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (A f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, A (T₂ f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hT₂ f) (hA (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (A (T₂ f)) f).2.2.2.1 _ hc (hid f))
  let T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d) :=
    LinearEquiv.ofLinear A T₂ (LinearMap.ext e12) (LinearMap.ext e21)
  set u := M.co.e.symm (fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (a i), fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (b i)) with hu_def
  have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm M a b
  set u' := mat (1 : UA σ X.J) * u * (mat k).transpose with hu'_def
  have hu' : At (evI F) u' := by
    intro c hc
    rw [hu'_def, ← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').1, GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').2, fun f => ?_⟩
  have hf : ActsD (evI F) (M.heisLine B.ψ u) f (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) := by
    refine (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u hu _ _).2 ?_
    rw [hu_def, LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]
  have ht := GlobalTheory.HeisTransport.actsD_heisLine_transport F E σ B n d X W M χX χW om r s r' s' hB hP.herm hP.skew hP.good hw
    1 h1 k hk1 T (fun f => hA f) (fun f => hT₂ f) u hu f _ hf
  exact (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u' hu' _ _).1 ht

end GlobalTheory.KInfComm

end
