import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingAdelicMatrixBoundedStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.ThKLevelCpt

theorem exists_compact_of_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (K : Set (AE F E)), IsCompact K →
    ∃ C : Set (UA σ J), IsCompact C ∧ ∀ g : UA σ J, (∀ i j, mat g i j ∈ K) → (∀ i j, mat g⁻¹ i j ∈ K) → g ∈ C := by
  intro F E _ _ _ _ _ σ d J K hK
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin d) (AE F E))) : Set (GL (Fin d) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin d) (AE F E) => (g : Matrix (Fin d) (Fin d) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))
      continuous_const
  let S : Set (Matrix (Fin d) (Fin d) (AE F E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin d) (Fin d) (AE F E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op)), fun g h1 h2 => ?_⟩
  exact ⟨fun i _ j _ => h1 i j, (mat g⁻¹), fun i _ j _ => h2 i j, rfl⟩

theorem isCompact_latLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.L.IsLattice E →
    IsCompact (GlobalTheory.ThKLevel.latLevel σ W : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d W hL
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ W.J => mat g⁻¹ := hm.comp continuous_inv
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.T.lattice_preserving_adelic_matrix_bounded F E d W hL
  obtain ⟨C, hC, hCe⟩ := exists_compact_of_entries F E σ d W.J K hK
  have hcl : IsClosed (GlobalTheory.ThKLevel.latLevel σ W : Set (UA σ W.J)) := by
    have h1 : IsClosed (GlobalTheory.ThKAdm.FinPt σ W) := isClosed_UAtSub (σ := σ) W (fun a : AF F => a.2)
    have h2 : IsClosed {k : UA σ W.J | ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
        mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun w => isClosed_iInter fun z => isClosed_iInter fun _ => ?_
      exact ((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hm.matrix_mulVec continuous_const)).inter
        ((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hmi.matrix_mulVec continuous_const))
    exact h1.inter h2
  refine hC.of_isClosed_subset hcl fun k hk => hCe k ?_ ?_
  · exact hKe (mat k) hk.1 (fun v z hz => (hk.2 v z hz).1)
  · have hk' : k⁻¹ ∈ GlobalTheory.ThKLevel.latLevel σ W := (GlobalTheory.ThKLevel.latLevel σ W).inv_mem hk
    exact hKe (mat k⁻¹) hk'.1 (fun v z hz => (hk'.2 v z hz).1)

end GlobalTheory.ThKLevelCpt

end
