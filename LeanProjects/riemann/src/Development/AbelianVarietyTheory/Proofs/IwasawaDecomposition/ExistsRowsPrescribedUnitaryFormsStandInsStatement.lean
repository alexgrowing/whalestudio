import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  first | exact @GlobalTheory.Mem.DfGen.exists_rowsRest_std | exact GlobalTheory.Mem.DfGen.exists_rowsRest_std | (intros; apply GlobalTheory.Mem.DfGen.exists_rowsRest_std <;> assumption)
