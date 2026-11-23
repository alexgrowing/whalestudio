import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.StdPairLoc

theorem insS_rank_le {R : Type} [Field R] {a b : ℕ} (Y : Matrix (Fin b) (Fin (a + b)) R)
    (r : Fin (a + (b + 2)) → R) (c : Fin b → R) (x : R) :
    (insS Y r c x).rank ≤ Y.rank + 2 := by
  classical
  let e : Fin (a + (b + 2)) → R := fun j => if j.1 = a + b + 1 then 1 else 0
  let gf : (Fin (a + b) → R) → (Fin (a + (b + 2)) → R) := fun v j =>
    if h₁ : j.1 < a then v ⟨j.1, by omega⟩ else if h₂ : j.1 = a then 0 else if h₃ : j.1 = a + b + 1 then 0 else
      v ⟨j.1 - 1, by have := j.2; omega⟩
  let g : (Fin (a + b) → R) →ₗ[R] (Fin (a + (b + 2)) → R) :=
    { toFun := gf
      map_add' := by
        intro v w; funext j; simp only [gf, Pi.add_apply]; split_ifs <;> simp
      map_smul' := by
        intro s v; funext j; simp only [gf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }
  have hsub : Submodule.span R (Set.range (insS Y r c x).row) ≤
      (Submodule.span R (Set.range Y.row)).map g ⊔ R ∙ e ⊔ R ∙ r := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change insS Y r c x i ∈ _
    by_cases i0 : i.1 = 0
    · refine Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨x, ?_⟩))
      funext j
      simp only [insS, e, i0, Pi.smul_apply, smul_eq_mul, dite_true]
      split_ifs <;> simp
    by_cases i1 : i.1 = b + 1
    · refine Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨1, ?_⟩)
      funext j
      simp [insS, i0, i1]
    · have hk : i.1 - 1 < b := by have := i.2; omega
      have hrow : insS Y r c x i = g (Y ⟨i.1 - 1, hk⟩) + c ⟨i.1 - 1, hk⟩ • e := by
        funext j
        simp only [insS, i0, i1, dite_false, g, gf, e, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        split_ifs <;> first | (exfalso; omega) | simp
      rw [hrow]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩))))
        (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))))
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  have h1 : Module.finrank R (R ∙ e) ≤ 1 := (finrank_span_le_card ({e} : Set _)).trans (by simp)
  have h2 : Module.finrank R (R ∙ r) ≤ 1 := (finrank_span_le_card ({r} : Set _)).trans (by simp)
  have h3 := Submodule.finrank_map_le g (Submodule.span R (Set.range Y.row))
  calc _ ≤ Module.finrank R ↥((Submodule.span R (Set.range Y.row)).map g ⊔ R ∙ e ⊔ R ∙ r) :=
        Submodule.finrank_mono hsub
    _ ≤ Module.finrank R ↥((Submodule.span R (Set.range Y.row)).map g ⊔ R ∙ e) + Module.finrank R (R ∙ r) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ Module.finrank R ↥((Submodule.span R (Set.range Y.row)).map g) + Module.finrank R (R ∙ e) +
          Module.finrank R (R ∙ r) := by
        gcongr; exact Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := by omega

end GlobalTheory.StdPairLoc
