import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilEqRank

variable {D : D7}

theorem equalRankSplittingCharsAdmissible_mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) :=
  ⟨h.1, h.2.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ' ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.2.1, resEta_mul h.2.2.2.2 h0⟩

theorem equalRankSplittingCharsAdmissible_mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' :=
  ⟨h.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.1, resEta_mul h.2.2.2.1 h0, h.2.2.2.2⟩

theorem exists_weilFun_eqRank : ∀ D : D7, WeilEx D → WeilOnEqEx D → WeilTwEq D → ∀ ψ, IsStdChar D ψ (-1) →
    ∃ Wf : WeilFun D ψ, Wf.EqRank := by
  classical
  intro D h1 h2 h3 ψ hψ
  obtain ⟨W₀⟩ := h1 ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W),
      (V.rank ≠ W.rank → om = W₀.om V W χ χ') ∧ (AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om) := fun V W χ χ' => by
    by_cases h : AdmE V W χ χ'
    · obtain ⟨om, hom⟩ := h2 ψ hψ V W χ χ' h
      exact ⟨om, fun hne => absurd h.1 hne, fun _ => hom⟩
    · exact ⟨W₀.om V W χ χ', fun _ => rfl, fun k => absurd k h⟩
  choose om hne heq using key
  refine ⟨⟨om, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_⟩, heq, fun V W χ χ' ν ha hν h0 => ?_, fun V W χ χ' ν ha hν h0 => ?_⟩
  · rw [hne V W χ χ' ha.1]; exact W₀.om_heis V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_aut V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_cont V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unit V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_split V W χ χ' ha
  · rw [hne V W χ χ' ha.1, hne V W χ (χ' * ν) ha.1]; exact W₀.twW V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne V W (χ * ν) χ' ha.1]; exact W₀.twV V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne W V χ' χ ha.1.symm]; exact W₀.om_swap V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unr V W χ χ' ha
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).1 _ (heq V W χ (χ' * ν) (equalRankSplittingCharsAdmissible_mul_right ha hν h0))
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).2 _ (heq V W (χ * ν) χ' (equalRankSplittingCharsAdmissible_mul_left ha hν h0))

end GlobalTheory.Mem.WeilEqRank

end
