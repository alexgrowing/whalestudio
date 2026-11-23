import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3Split

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem isLabElt_of_isTEnv : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  intro D V Pl0 pl ok i x
  refine ⟨fun hk h => ?_, fun h => ?_, splitLab_pairwise _ _⟩
  · obtain ⟨α, ⟨e, ϖ, he, h1, h2, hα⟩, hx⟩ := h hk
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    obtain ⟨hf1, hf2, -⟩ := H.2.2.1 _ _ _ hI
    obtain ⟨⟨L, hL⟩, -⟩ := H.1 _ hf1 hf2
    exact ⟨e, e + cA D e, ϖ, α⁻¹, hI, h1, h2, inv_mem hα.1, hx, (hL _).1 (inv_mem ((hL _).2 hα.2.1)),
      GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V _ e ϖ _ α he h1 h2 hk hα⟩
  · obtain ⟨e, α, he, hα, hs, hx⟩ := h
    exact ⟨e, e + cA D e, α, Or.inl ⟨he, rfl⟩, hα, hx, hs⟩

end GlobalTheory.Hk3Split
