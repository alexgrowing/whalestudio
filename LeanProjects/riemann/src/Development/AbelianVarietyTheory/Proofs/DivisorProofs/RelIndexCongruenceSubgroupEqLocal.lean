import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHomMapsCongruenceSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCongruenceHomSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNextCongruenceOfLocalStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamCnt

theorem relIndex_congG_succ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    (GlobalTheory.TamCnt.congG σ J Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.congG σ J Λ v k) =
      (GlobalTheory.TamCnt.locCong σ J Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.locCong σ J Λ v k) := by
  let f : congG σ J Λ v k →* locCong σ J Λ v k :=
    ((locHom σ J v).comp (congG σ J Λ v k).subtype).codRestrict _
      (fun h => GlobalTheory.T.local_hom_maps_congruence_subgroup F E σ M J Λ v k h.1 h.2)
  have hf : Function.Surjective f := fun g => by
    obtain ⟨h, hh, e⟩ := GlobalTheory.T.local_congruence_hom_surjective F E σ M J Λ v k g.1 g.2
    exact ⟨⟨h, hh⟩, Subtype.ext e⟩
  have hc : ((locCong σ J Λ v (k + 1)).subgroupOf (locCong σ J Λ v k)).comap f =
      (congG σ J Λ v (k + 1)).subgroupOf (congG σ J Λ v k) := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      exact GlobalTheory.T.mem_next_congruence_of_local F E σ M J Λ v k h.1 h.2 hh
    · intro hh
      exact GlobalTheory.T.local_hom_maps_congruence_subgroup F E σ M J Λ v (k + 1) h.1 hh
  unfold Subgroup.relIndex
  rw [← hc, Subgroup.index_comap_of_surjective _ hf]

end GlobalTheory.TamCnt
