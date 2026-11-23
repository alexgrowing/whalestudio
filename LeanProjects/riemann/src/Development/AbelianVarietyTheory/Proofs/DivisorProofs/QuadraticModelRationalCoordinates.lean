import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RatCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_injective {κ : Type} : Function.Injective (hat (F := F) (κ := κ)) := by
  intro w w' h
  have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
  simp only [hat, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  · exact hinj (congrFun h1 i)
  · exact hinj (congrFun h2 i)

theorem hat_add {κ : Type} (w w' : (κ → F) × (κ → F)) : hat (w + w') = hat w + hat w' := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; rfl

theorem hat_smul {κ : Type} (c : F) (w : (κ → F) × (κ → F)) :
    hat (c • w) = algebraMap F (AF F) c • hat w := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem incM_add {m k : Type} (x x' : Matrix m k E) : incM F (x + x') = incM F x + incM F x' := by
  ext i j; simp [incM]

theorem incM_smul' {m k : Type} (c : F) (x : Matrix m k E) :
    incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  show (1 : AF F) ⊗ₜ[F] (c • x i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] x i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem incM_injective {m k : Type} : Function.Injective (incM F (E := E) (m := m) (n := k)) := by
  intro x x' h
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  ext i j
  exact hinj (congrFun (congrFun h i) j)

end GlobalTheory.RatCoord

open GlobalTheory.RatCoord in
theorem GlobalTheory.RatCoord.ratEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → Module.finrank F E = 2 → ∃ Φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x, M.co.e (incM F x) = ((fun i => algebraMap F (AF F) ((Φ x).1 i)), (fun i => algebraMap F (AF F) ((Φ x).2 i))) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM hE
  classical
  let Φ₀ : Matrix (Fin n) (Fin d) E → (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    fun x => ((hM.rat x).choose, (hM.rat x).choose_spec.choose)
  have hΦ₀ : ∀ x, M.co.e (incM F x) = hat (Φ₀ x) := fun x => (hM.rat x).choose_spec.choose_spec
  let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := Φ₀
      map_add' := fun x x' => by
        apply hat_injective
        rw [hat_add, ← hΦ₀, ← hΦ₀, ← hΦ₀, incM_add, map_add]
      map_smul' := fun c x => by
        apply hat_injective
        rw [RingHom.id_apply, hat_smul, ← hΦ₀, ← hΦ₀, incM_smul', LinearEquiv.map_smul] }
  have hinj : Function.Injective L := by
    intro x x' h
    apply incM_injective (F := F)
    apply M.co.e.injective
    rw [hΦ₀, hΦ₀]
    exact congrArg hat h
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hrank : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hE,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ring
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun x => ?_⟩
  exact hΦ₀ x
