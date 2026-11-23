import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SplitUnitLiftCont

open GlobalTheory.SplitGLLift GlobalTheory.SplitUnitLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem continuous_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous (liftPair h τ) := by
  have hj : Continuous (LinearMap.inr F (Ainf F) (Af F) ∘ₗ GlobalTheory.AdelicU.singleFin v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  have h1 : Continuous (GlobalTheory.AdelicU.Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ hj
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have h2 : Continuous ((splitAlgEquiv h τ).symm : Fv F v × Fv F v → Fv F v ⊗[F] E) :=
    IsModuleTopology.continuous_of_linearMap (splitAlgEquiv h τ).symm.toLinearMap
  exact h1.comp h2

theorem continuous_liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} :
    Continuous (liftMat (n := Fin n) h τ) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) =>
    liftPair h τ (p.1 i j, p.2 i j)
  exact (continuous_liftPair h τ).comp
    (((continuous_fst.matrix_elem i j)).prodMk (continuous_snd.matrix_elem i j))

theorem continuous_liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map τ).det) : Continuous (liftN h τ J hJ) := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hp : Continuous (pairHom (J.map τ) hJ) := by
    show Continuous fun g : GL (Fin n) (Fv F v) => ((g : Matrix (Fin n) (Fin n) (Fv F v)),
      (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)
    refine Units.continuous_val.prodMk ?_
    exact (continuous_const.matrix_mul (Units.continuous_coe_inv.matrix_transpose)).matrix_mul continuous_const
  show Continuous fun g => 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1)
  exact continuous_const.add ((continuous_liftMat h τ).comp (hp.sub continuous_const))

theorem continuous_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Continuous (liftU h τ J ε herm hJ) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_liftN h τ J hJ, ?_⟩
  exact (continuous_liftN h τ J hJ).comp continuous_inv

theorem tendsto_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Tendsto (liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  have := (continuous_liftU h τ J ε herm hJ).tendsto 1
  rwa [map_one] at this

theorem tendsto_liftU_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := fun h τ J ε herm hJ => tendsto_liftU h τ J ε herm hJ

end GlobalTheory.SplitUnitLiftCont

end
