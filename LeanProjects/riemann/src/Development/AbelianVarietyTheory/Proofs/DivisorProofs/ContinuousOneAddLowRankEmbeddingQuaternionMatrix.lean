import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory

theorem emb_qm_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  intro F E _ _ _ _ a b M A B θ
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  have hL : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => c * y) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hR : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => y * c) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (AF F) c)
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have hc : ∀ i, Continuous fun x : DA F a b => coords x i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have h0 : Continuous fun x : DA F a b => x.re := by simpa [coords] using hc 0
  have h1 : Continuous fun x : DA F a b => x.imI := by simpa [coords] using hc 1
  have h2 : Continuous fun x : DA F a b => x.imJ := by simpa [coords] using hc 2
  have h3 : Continuous fun x : DA F a b => x.imK := by simpa [coords] using hc 3
  have hq : ∀ k l, Continuous fun x : DA F a b => qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [qm]
    · exact (hι.comp h0).add ((hR θ).comp (hι.comp h1))
    · exact (hL _).comp ((hι.comp h2).add ((hR θ).comp (hι.comp h3)))
    · exact (hι.comp h2).sub ((hR θ).comp (hι.comp h3))
    · exact (hι.comp h0).sub ((hR θ).comp (hι.comp h1))
  apply continuous_matrix
  intro i j
  simp only [emb, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply]
  refine continuous_const.add (continuous_finset_sum _ fun l _ => (hR _).comp
    (continuous_finset_sum _ fun k _ => (hL _).comp ((hq k l).sub continuous_const)))

end GlobalTheory
