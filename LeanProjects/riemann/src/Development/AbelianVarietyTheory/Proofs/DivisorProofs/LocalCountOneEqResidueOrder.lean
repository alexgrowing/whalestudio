import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCountEqCardCongruenceQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitaryConjugateTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIdealSmulMemIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntegersQuotientSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteLocalExtensionIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalTraceOneElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselLiftSpecialUnitaryMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSpecialUnitarySplitEqSLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardReductionUnitaryEqSuMatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryConjugateTransposeJStatement

noncomputable section

namespace GlobalTheory.TamOne

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

theorem locCount_one_eq_resOrder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v 1 = resOrder E r v := by
  intro E _ _ _ r G Λ _ hU hSD v
  obtain ⟨h, hh, hΛ⟩ := GlobalTheory.T.exists_local_unitary_conjugate_transpose E r G Λ hU hSD v
  have hPΛ := GlobalTheory.T.local_lattice_ideal_smul_mem_iff Λ (extIdeal v) v h hΛ
  obtain ⟨ρ, hρs, hρι, hρk⟩ := GlobalTheory.T.local_integers_quotient_surjection E hU v
  have hcpl := GlobalTheory.T.isAdicComplete_local_extension_ideal E hU v
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_local_trace_one_element E hU v
  have hIc : ∀ x ∈ (extIdeal v).map (intLocIncl (E := E) v),
      intLocConj v x ∈ (extIdeal v).map (intLocIncl (E := E) v) := by
    intro x hx
    have h1 : Ideal.map (intLocConj v) ((extIdeal v).map (intLocIncl (E := E) v)) ≤
        (extIdeal v).map (intLocIncl (E := E) v) := by
      rw [Ideal.map_map]
      have e : (intLocConj v).comp (intLocIncl v) =
          (intLocIncl v).comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) :=
        RingHom.ext (intLocConj_intLocIncl v)
      rw [e, ← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 (extIdeal_le_comap v))
    exact h1 (Ideal.mem_map_of_mem _ hx)
  have hρc : ∀ z, ρ (intLocConj v z) = resConj v (ρ z) := by
    intro z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ρ z)
    have hz : z - intLocIncl v x ∈ (extIdeal v).map (intLocIncl (E := E) v) :=
      (hρk _).1 (by rw [map_sub, hρι, hx, sub_self])
    have hz' := (hρk _).2 (hIc _ hz)
    rw [map_sub, map_sub, intLocConj_intLocIncl, hρι, sub_eq_zero] at hz'
    rw [hz', ← hx, resConj_mk]
  have hlift : ∀ g ∈ suMat (𝓞 E ⧸ extIdeal v) (resConj v) r,
      ∃ g' ∈ suMat (intLoc (maximalRealSubfield E) E v) (intLocConj v) r, g'.map ρ = g := by
    intro g hg
    choose g0 hg0 using fun a b => hρs (g a b)
    let g0m : Matrix (Fin r) (Fin r) (intLoc (maximalRealSubfield E) E v) := Matrix.of g0
    have hm : g0m.map ρ = g := Matrix.ext fun a b => hg0 a b
    have h1 : ∀ a b, ((g0m.map (intLocConj v))ᵀ * g0m - 1) a b ∈ (extIdeal v).map (intLocIncl (E := E) v) := by
      intro a b
      refine (hρk _).1 ?_
      have key : ((g0m.map (intLocConj v))ᵀ * g0m - 1).map ρ = (g.map (resConj v))ᵀ * g - 1 := by
        have hmc : (g0m.map (intLocConj v)).map ρ = g.map (resConj v) := by
          rw [← hm, Matrix.map_map, Matrix.map_map]
          exact congrArg g0m.map (funext hρc)
        rw [← RingHom.mapMatrix_apply, map_sub, map_mul, map_one, RingHom.mapMatrix_apply,
          RingHom.mapMatrix_apply, Matrix.transpose_map, hmc, hm]
      rw [hg.1, sub_self] at key
      exact congrArg (fun M => M a b) key
    have h2 : g0m.det - 1 ∈ (extIdeal v).map (intLocIncl (E := E) v) := by
      refine (hρk _).1 ?_
      rw [map_sub, map_one, RingHom.map_det, RingHom.mapMatrix_apply, hm, hg.2, sub_self]
    obtain ⟨g', hu, hd, hc⟩ := GlobalTheory.T.hensel_lift_special_unitary_matrix (intLocConj v) (intLocConj_intLocConj v) _ hIc hcpl w hw r g0m h1 h2
    refine ⟨g', ⟨hu, hd⟩, Matrix.ext fun a b => ?_⟩
    have := (hρk _).2 (hc a b)
    rw [map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    exact hg0 a b
  have hg := GlobalTheory.T.locCount_eq_card_congruence_quotient (cj E) Gᵀ Λ hSD.2.2.1 v 1
  simp only [pow_one] at hg
  refine hg.trans ((GlobalTheory.T.local_unitary_conjugate_transpose_J E r G Λ v h hh hΛ hPΛ ρ hρk hρc hlift).trans ?_)
  unfold resOrder
  split_ifs with hP
  · exact (GlobalTheory.T.card_reduction_unitary_eq_suMat E r v).symm
  · exact GlobalTheory.T.card_special_unitary_split_eq_SL E r hU v hP

end GlobalTheory.TamOne
