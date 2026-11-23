import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchPartFinIncl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmArchimedeanSplitBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleArchimedeanInclusionContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleIntegersScaleSmallStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.ArchFinSplit

theorem exists_cm_adele_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), IsCMExt F E σ → ∃ Φ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F), (∀ x : E, Φ (inclR (F := F) (AF F) x) = (fun w => (B.emb w).1 x, Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)) ∧ (∀ z w, (Φ z).1 w = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w) z) ∧ (∀ z, Φ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = (fun w => star ((Φ z).1 w), Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) (Φ z).2)) ∧ (∀ (u : AF F) z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0 → (Φ z).2 = 0 → u • z = 0) ∧ (∀ (u : AF F) z, u.2 = 0 → (Φ z).1 = 0 → u • z = 0) ∧ Continuous (fun c : InfinitePlace F → ℂ => Φ.symm (c, 0)) ∧ ∀ U ∈ nhds (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), ∃ N : ℕ, 1 ≤ N ∧ ∀ y ∈ Formalism.MainNotions.S.IntAf F E, Φ.symm (0, (N : E ⊗[F] Formalism.MainNotions.S.Af F) * y) ∈ U := by
  have hS1 := GlobalTheory.T.cm_archimedean_split_bijective
  have hS2 := GlobalTheory.T.adele_archimedean_inclusion_continuous
  have hS3 := GlobalTheory.T.finite_adele_integers_scale_small
  intro F E _ _ _ _ _ σ B h
  have hR := h.1
  let Φ := RingEquiv.ofBijective _ (hS1 F E σ B.emb h)
  have hΦ : ∀ z, Φ z = (fun w => piInf (B.emb w) z, GlobalTheory.ArchFinSplit.finPart F E z) := fun z => rfl
  have halg : ∀ u : AdeleRing (𝓞 F) F, Φ (algebraMap (AdeleRing (𝓞 F) F) (AE F E) u) =
      (fun w => InfinitePlace.Completion.extensionEmbedding w (u.1 w), (1 : E) ⊗ₜ[F] u.2) := by
    intro u
    rw [hΦ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    refine Prod.ext (funext fun w => ?_) rfl
    show InfinitePlace.Completion.extensionEmbedding w (u.1 w) * (B.emb w).1 1 = _
    rw [map_one, mul_one]
  have hfin : ∀ y, Φ.symm (0, y) = GlobalTheory.ArchFinSplit.finIncl F E y := fun y => by
    rw [RingEquiv.symm_apply_eq, hΦ]
    exact Prod.ext (GlobalTheory.ArchFinSplit.archPart_finIncl B.emb y).symm (GlobalTheory.ArchFinSplit.finPart_finIncl y).symm
  refine ⟨Φ, fun x => ?_, fun z w => rfl, fun z => ?_, fun u z hu hz => ?_, fun u z hu hz => ?_,
    hS2 F E hR Φ fun u hu => by rw [halg, hu, TensorProduct.tmul_zero], fun U hU => ?_⟩
  · rw [hΦ]
    refine Prod.ext (funext fun w => ?_) rfl
    show InfinitePlace.Completion.extensionEmbedding w ((1 : AdeleRing (𝓞 F) F).1 w) * (B.emb w).1 x = _
    rw [show (1 : AdeleRing (𝓞 F) F).1 w = 1 from rfl, map_one, one_mul]
  · rw [hΦ, hΦ]
    refine Prod.ext (funext fun w => GlobalTheory.WrongSignPair.piInf_cA h (B.emb w) z) ?_
    show GlobalTheory.ArchFinSplit.finPart F E (cA σ z) = Formalism.UG.sigR σ _ (GlobalTheory.ArchFinSplit.finPart F E z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  · have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    apply Φ.injective
    rw [map_zero, Algebra.smul_def, map_mul, halg]
    refine Prod.ext (funext fun w => ?_) ?_
    · show InfinitePlace.Completion.extensionEmbedding w (u.1 w) * (Φ z).1 w = 0
      rw [h1]
      show InfinitePlace.Completion.extensionEmbedding w (0 : w.Completion) * (Φ z).1 w = 0
      rw [map_zero, zero_mul]
    · simp [hz]
  · apply Φ.injective
    rw [map_zero, Algebra.smul_def, map_mul, halg, hu]
    refine Prod.ext (funext fun w => ?_) ?_
    · simp [hz]
    · simp
  · obtain ⟨N, hN, hy⟩ := hS3 F E U hU
    exact ⟨N, hN, fun y hy' => by rw [hfin]; exact hy y hy'⟩

end GlobalTheory.ArchFinSplit
