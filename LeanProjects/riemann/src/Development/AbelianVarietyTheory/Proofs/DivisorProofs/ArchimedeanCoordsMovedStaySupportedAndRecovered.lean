import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem at_mul_of_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d : ℕ} (G : Matrix (Fin n) (Fin n) (AE F E)) (H : Matrix (Fin d) (Fin d) (AE F E))
    (L : Matrix (Fin n) (Fin d) (AE F E)) (hL : At (evI F) L) : At (evI F) (G * L * Hᵀ) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hL u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_infAd_of_evI {F : Type} [Field F] [NumberField F] (u : AF F) (hu : evI F u = 0)
    (α : mixedEmbedding.mixedSpace F) : u * infAd F α = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
  refine Prod.ext ?_ ?_
  · show u.1 * _ = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem eq_infAd_of_ann {F : Type} [Field F] [NumberField F] (z : AF F)
    (hz : ∀ a : AF F, evI F a = 0 → a * z = 0) : z = infAd F (evI F z) := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : AF F, a.1 = 0 ∧ a.2 = 1 := ⟨(0, 1), rfl, rfl⟩
  have h0 : evI F a = 0 := by
    have e : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 := rfl
    rw [e, ha1, map_zero]
  have h2 : z.2 = 0 := by
    have h3 := congrArg Prod.snd (hz a h0)
    have h4 : (a * z).2 = a.2 * z.2 := rfl
    rw [h4, ha2, one_mul] at h3
    exact h3
  refine Prod.ext ?_ ?_
  · show z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1)
    rw [RingEquiv.symm_apply_apply]
  · show z.2 = 0
    exact h2

theorem liftI_at_movI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), At (evI F) (liftI M ζ) ∧ liftI M (movI M p ζ) = actAB (cA σ) p⁻¹ (liftI M ζ) := by
  intro F E _ _ _ _ _ σ n d X W M p ζ
  have hL : At (evI F) (liftI M ζ) := by
    intro u hu
    unfold liftI
    rw [← LinearEquiv.map_smul]
    convert (M.co.e.symm).map_zero using 2
    refine Prod.ext ?_ ?_
    · funext i
      exact mul_infAd_of_evI u hu _
    · funext i
      exact mul_infAd_of_evI u hu _
  refine ⟨hL, ?_⟩
  have hw : At (evI F) (actAB (cA σ) p⁻¹ (liftI M ζ)) := at_mul_of_at _ _ _ hL
  set w := actAB (cA σ) p⁻¹ (liftI M ζ) with hwdef
  have hc : ∀ u : AF F, evI F u = 0 → u • M.co.e w = 0 := by
    intro u hu
    rw [← LinearEquiv.map_smul, hw u hu, LinearEquiv.map_zero]
  unfold liftI movI arch
  conv_rhs => rw [← M.co.e.symm_apply_apply w]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.fst (hc a ha)) i).symm
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.snd (hc a ha)) i).symm

end GlobalTheory.ArchDecay
