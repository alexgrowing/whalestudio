import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

namespace GlobalTheory.ThK.LemF.QuotInv.KAtCompact

theorem kAt_compact_secondCountable_t2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    CompactSpace (KAt K (evFin F v)) ∧ SecondCountableTopology (KAt K (evFin F v)) ∧ T2Space (KAt K (evFin F v)) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' om₁ om₁' hT _ v K hK
  obtain ⟨_, _, hsc, ht2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  have hc : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
    have e : K = GlobalTheory.StabHaar.stabK B G.V := by
      ext g
      rw [hK g, GlobalTheory.StabHaar.isStab_stabK B G.V g]
    subst e
    exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hT.geo.hV.lat)) hsub
  exact ⟨isCompact_iff_compactSpace.mp (isCompact_KAt hc _), inferInstance, inferInstance⟩

end GlobalTheory.ThK.LemF.QuotInv.KAtCompact
