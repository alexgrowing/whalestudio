import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

theorem tendsto_idem_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : AE F E),
    (∀ u : AF F, At (evI F) u → u • c = 0) →
    Tendsto (fun T : Finset (Pl F) => GlobalTheory.TruncFix.idem T • c) atTop (𝓝 c) := by
  intro F E _ _ _ _ _ c hc
  classical
  have hinf : At (evI F) (pairA F 1 0) := by
    intro u hu
    have h1 : u.1 = 0 := by
      have hu' : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu'
    exact Prod.ext (by change u.1 * 1 = 0; rw [h1, zero_mul]) (by change u.2 * 0 = 0; exact mul_zero _)
  have hc' : pairA F 0 1 • c = c := by
    have e : pairA F 0 1 = 1 - pairA F 1 0 :=
      Prod.ext (sub_self (1 : Ainf F)).symm (sub_zero (1 : Af F)).symm
    rw [e, sub_smul, one_smul, hc _ hinf, sub_zero]
  have hidem : ∀ T : Finset (Pl F), idem T = pairA F 0 (∑ v ∈ T, GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) := by
    intro T
    unfold idem
    exact (map_sum (LinearMap.inr F (Ainf F) (Af F)) (fun v => GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) T).symm
  have h1 : ∀ v : Pl F, evalV F v (GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) = 1 := fun v =>
    GlobalTheory.AdelicU.evalV_singleFin_self v 1
  have h0 : ∀ v v' : Pl F, v' ≠ v → evalV F v' (GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) = 0 := fun v v' h =>
    GlobalTheory.AdelicU.evalV_singleFin_ne h 1
  have ht := GlobalTheory.VecInv.tendsto_sum_placeIdem (fun v => GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) h1 h0
  have hp : Continuous fun β : Af F => pairA F 0 β := continuous_const.prodMk continuous_id
  have hm : Continuous fun a : AF F => a • c := continuous_id.smul continuous_const
  have h : Tendsto (fun T : Finset (Pl F) => pairA F 0 (∑ v ∈ T, GlobalTheory.AdelicU.singleFin v (1 : Fv F v)) • c) atTop
      (𝓝 (pairA F 0 1 • c)) := ((hm.comp hp).tendsto 1).comp ht
  rw [hc'] at h
  exact h.congr fun T => by rw [hidem]

end GlobalTheory.TruncFix

end
