import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFunctionStabilizerIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt

namespace GlobalTheory.IwasawaInf

theorem exists_stab_mul_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ g ∈ UAt σ X (evI F), ∃ p ∈ UAt σ X (evI F), (∃ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x) ∧
      ∃ k ∈ KAt K (evI F), g = p * k := by
  intro F E _ _ _ _ _ σ B b X X₁ H i₀ i₁ r s hB hX hH K hK g hg
  obtain ⟨p, ⟨l, hl⟩, k, hk, e⟩ := GlobalTheory.IwLine.iwasawa B hB hX hH g
  refine ⟨GlobalTheory.KAvg.prH σ X.J (GlobalTheory.KAvg.idem_realAd F) p, GlobalTheory.KAvg.prH_mem p,
    ⟨_, GlobalTheory.KAvg.prH_mulVec _ hl⟩, GlobalTheory.KAvg.prH σ X.J (GlobalTheory.KAvg.idem_realAd F) k,
    GlobalTheory.KAvg.prH_mem_KAt hK ((hK k).2 hk), ?_⟩
  rw [← map_mul, ← e, GlobalTheory.KAvg.prH_of_mem hg]

end GlobalTheory.IwasawaInf
