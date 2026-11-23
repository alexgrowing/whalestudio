import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCubeVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerRelativelyCompactStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.UnipInv

theorem isCompact_stabAt_mat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) (x : Fin n → E) (P : Set (Matrix (Fin n) (Fin n) (AE F E))),
    IsCompact P → IsCompact {g : stabAt σ Y ev x | mat g.1.1 ∈ P ∧ mat g.1.1⁻¹ ∈ P} := by
  intro F E _ _ _ _ _ σ n Y R _ ev x P hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hcA : Continuous (cA (F := F) (E := E) σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have h1 : Topology.IsClosedEmbedding (fun g : stabAt σ Y ev x => (g.1.1 : GL (Fin n) (AE F E))) :=
    ((GlobalTheory.UnitaryAdelicTop.isClosed_UG (cA σ) hcA (incM F Y.J)).isClosedEmbedding_subtypeVal.comp
      (isClosed_UAtSub Y ev).isClosedEmbedding_subtypeVal).comp (isClosed_stabAt_vec Y ev x).isClosedEmbedding_subtypeVal
  have h2 := Units.isClosedEmbedding_embedProduct.comp h1
  have h3 := (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (AE F E))).symm.isCompact_preimage.2 hP
  exact h2.isCompact_preimage (hP.prod h3)

theorem map_mul_right_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure →
    ∀ q : stabAt σ G.V (evFin F v) H.x, q.1.1 ∈ unip σ G.V H → Measure.map (· * q) μ = μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT _ v μ hμ q hq
  haveI := hμ
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  haveI := hTG; haveI := hLC; haveI := hSC; haveI := hT2
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UAtSub σ G.V (evFin F v)) :=
    (isClosed_UAtSub G.V (evFin F v)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (stabAt σ G.V (evFin F v) H.x) :=
    (isClosed_stabAt_vec G.V (evFin F v) H.x).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hnil := GlobalTheory.T.unipotent_radical_cube_vanishes F E σ B (b + 2) b G.V G₁.V H 0 (b + 1) _ _ (GlobalTheory.UnipHaar.sigma_invol hT.base.cm)
    hT.geo.hV hC.hH q.1.1 hq
  obtain ⟨P, hP, hPq⟩ := GlobalTheory.T.unipotent_stabilizer_relatively_compact F E σ (b + 2) G.V v H.x q hnil
  have hCc := isCompact_stabAt_mat F E σ (b + 2) G.V (evFin F v) H.x P hP
  set K := (Subgroup.zpowers q).topologicalClosure with hK
  have hsub : ((Subgroup.zpowers q : Subgroup _) : Set (stabAt σ G.V (evFin F v) H.x)) ⊆
      {g : stabAt σ G.V (evFin F v) H.x | mat g.1.1 ∈ P ∧ mat g.1.1⁻¹ ∈ P} := fun g hg => hPq g hg
  have hKc : IsCompact (K : Set (stabAt σ G.V (evFin F v) H.x)) :=
    hCc.of_isClosed_subset isClosed_closure (closure_minimal hsub hCc.isClosed)
  have hqK : q ∈ K := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers q)
  exact GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hKc q hqK

end GlobalTheory.ThK.LemF.QuotInv.UnipInv
