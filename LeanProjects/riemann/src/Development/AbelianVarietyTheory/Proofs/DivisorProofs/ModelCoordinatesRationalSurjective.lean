import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RatDarbSurj

theorem rat_surj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (hB : B.IsGood σ) (hM : M.IsGood B.ψ)
    (y z : Fin n × Fin d → F) : ∃ x : Matrix (Fin n) (Fin d) E,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  have hA : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  haveI : Nontrivial (AF F) := hA.nontrivial
  have hR : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective hA

  let e' : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun x => M.co.e (incM F x)
      map_add' := fun x x' => by
        rw [← map_add]
        congr 1
        ext i j
        simp [incM, Matrix.map_apply]
      map_smul' := fun c x => by
        have h : incM F (c • x) = algebraMap F (AF F) c • incM F x := by
          ext i j
          simp only [incM, Matrix.map_apply, Matrix.smul_apply]
          rw [Algebra.smul_def, map_mul, Algebra.smul_def]
          simp [inclR, Algebra.TensorProduct.algebraMap_apply]
        rw [h, map_smul]
        ext i <;> simp [Algebra.smul_def] }
  have he'_apply : ∀ x, e' x = M.co.e (incM F x) := fun x => rfl
  have he' : Function.Injective e' := fun x x' h => by
    rw [he'_apply, he'_apply] at h
    have h2 := M.co.e.injective h
    ext i j
    exact hR (congrFun (congrFun h2 i) j)

  let j : (Fin n × Fin d → F) × (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    ((Algebra.linearMap F (AF F)).compLeft (Fin n × Fin d)).prodMap ((Algebra.linearMap F (AF F)).compLeft (Fin n × Fin d))
  have hj_apply : ∀ y z : Fin n × Fin d → F,
      j (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun y z => rfl
  have hj : Function.Injective j := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    rw [hj_apply, hj_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hA (congrFun h.1 i)) (funext fun i => hA (congrFun h.2 i))
  have hle : LinearMap.range e' ≤ LinearMap.range j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hM.rat x
    exact ⟨(y, z), by rw [hj_apply, he'_apply, h]⟩
  have hE : Module.finrank F E = 2 := hB.cm.2.2.1
  have hfin : Module.finrank F (LinearMap.range e') = Module.finrank F (LinearMap.range j) := by
    rw [LinearMap.finrank_range_of_inj he', LinearMap.finrank_range_of_inj hj, Module.finrank_matrix, hE,
      Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hmem : j (y, z) ∈ LinearMap.range e' := heq ▸ LinearMap.mem_range_self j (y, z)
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, by rw [← he'_apply, hx, hj_apply]⟩

end GlobalTheory.RatDarbSurj
