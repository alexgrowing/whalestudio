import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.ThK.UnipDom

theorem isCompact_setOf_mat_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (Matrix (Fin n) (Fin n) (AE F E))) (hC : IsCompact C) :
    IsCompact {g : UA σ J | mat g ∈ C ∧ mat g⁻¹ ∈ C} := by
  classical
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hM : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Mᵀ * incM F J * M.map (cA σ) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hc)
  have hclosed : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (hM.comp Units.continuous_val) continuous_const
  have hφ : Topology.IsClosedEmbedding
      (fun g : UA σ J => Units.embedProduct (Matrix (Fin n) (Fin n) (AE F E)) g.1) :=
    Units.isClosedEmbedding_embedProduct.comp hclosed.isClosedEmbedding_subtypeVal
  have hK := hφ.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  rw [show MulOpposite.op '' C = MulOpposite.unop ⁻¹' C from
    Set.ext fun x => ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h => ⟨x.unop, h, rfl⟩⟩] at hK
  convert hK using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op]
  rfl

end GlobalTheory.ThK.UnipDom
