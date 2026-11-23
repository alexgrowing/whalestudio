import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.ThK.ConeEuler.StabCompAt

theorem compAt_mem_of_isStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J)), IsStab B K →
    ∀ k ∈ K, ∀ v : Pl F, compAt σ X.J v k ∈ K := by
  intro F E _ _ _ _ _ σ B n X K hK k hk v
  exact (GlobalTheory.ThK.ConeEuler.StabComp.comp_mem_of_isStab F E σ B n X K hK k hk).1 v

end GlobalTheory.ThK.ConeEuler.StabCompAt
