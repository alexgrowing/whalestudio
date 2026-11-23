import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem ratCoord_linear_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  intro F E _ _ _ _ _ σ n d X W M h
  choose y z hyz using h
  have hA : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  have hg : ∀ x, hat ((y x, z x) : (Fin n × Fin d → F) × (Fin n × Fin d → F)) = M.co.e (incM F x) :=
    fun x => (hyz x).symm
  have hinj : Function.Injective (hat : (Fin n × Fin d → F) × (Fin n × Fin d → F) → _) := by
    intro a b hab
    simp only [hat, Prod.mk.injEq] at hab
    exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))
  have hadd : ∀ x x' : Matrix (Fin n) (Fin d) E, incM F (x + x') = incM F x + incM F x' := by
    intro x x'
    ext i j
    simp [incM, Matrix.map_apply, map_add]
  have hsmul : ∀ (c : F) (x : Matrix (Fin n) (Fin d) E), incM F (c • x) = algebraMap F (AF F) c • incM F x := by
    intro c x
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.smul_apply]
    show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (c • x i j) =
      algebraMap F (AF F) c • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (x i j)
    rw [map_smul, algebraMap_smul]
  have hI : Function.Injective (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E)) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective hA)
  refine ⟨{ toFun := fun x => (y x, z x), map_add' := ?_, map_smul' := ?_ }, ?_, hg⟩
  · intro x x'
    apply hinj
    rw [hat_add, hg, hg, hg, hadd, map_add]
  · intro c x
    apply hinj
    rw [RingHom.id_apply, hat_smul, hg, hg, hsmul, LinearEquiv.map_smul]
  · intro x x' hx
    apply hI
    apply M.co.e.injective
    rw [← hg, ← hg]
    exact congrArg hat hx

end GlobalTheory.MixedLagr
