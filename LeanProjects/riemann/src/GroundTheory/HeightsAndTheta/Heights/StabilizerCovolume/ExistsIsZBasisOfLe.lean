import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CardZBasisEqMulFinrank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Module
open scoped Matrix

theorem exists_isZBasis_of_le {Em : Type} [Field Em] [NumberField Em] {N : ℕ}
    {I L : Submodule (𝓞 Em) (Fin N → Em)} (hIL : I ≤ L) (hfg : (L.restrictScalars ℤ).FG) :
    ∃ m, ∃ b : Fin m → Fin N → Em, IsZBasis I b := by
  have hle : I.restrictScalars ℤ ≤ L.restrictScalars ℤ := hIL
  haveI : Module.Finite ℤ (L.restrictScalars ℤ) := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (I.restrictScalars ℤ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let bI := Module.finBasis ℤ (I.restrictScalars ℤ)
  refine ⟨_, fun k => (bI k : Fin N → Em), ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact bI.linearIndependent.map' (I.restrictScalars ℤ).subtype (Submodule.ker_subtype _)
  · have h := congrArg Subtype.val (bI.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have hsp : Submodule.span ℤ (Set.range fun k => (bI k : Fin N → Em)) ≤ I.restrictScalars ℤ :=
      Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (bI k).2)
    exact hsp hx

theorem UnitaryCovolume.proof : UnitaryCovolume.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz I hIL hI _ ρ v hv
  have hex := exists_isZBasis_of_le hIL D.herm.fg
  have hnz : ∃ ρ' v', IsNzFamily I ρ' v' := ⟨ρ, v, hv⟩
  have hn := D.herm.finrank_eq_two_mul_card_cm
  have hpos : 0 < finrank ℚ Em := Module.finrank_pos
  have key : ∀ ρ' (v' : Fin ρ' → Fin D.N → Em), IsNzFamily I ρ' v' →
      D.covolZ z I = (∏ τ, (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v').det.re) /
          ((Submodule.span (𝓞 Em) (Set.range v')).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) *
        rootDiscr Em ^ (D.f * ρ) := by
    intro ρ' v' hv'
    obtain ⟨m, b, hb⟩ := hex
    have h1 := card_zBasis_eq_mul_finrank hv hb
    have h2 := card_zBasis_eq_mul_finrank hv' hb
    have hρ : ρ' = ρ := Nat.eq_of_mul_eq_mul_right hpos (h2.symm.trans h1)
    subst hρ
    rw [D.covolZ_eq_of_family hz hI hv' ⟨m, b, hb⟩]
    congr 1
    rw [rootDiscr, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hn]
    congr 1
    have hf : D.f = Fintype.card Ψ := rfl
    have hc : (Fintype.card Ψ : ℝ) ≠ 0 := by
      have : 0 < Fintype.card Ψ := by omega
      positivity
    rw [hf]
    push_cast
    field_simp
  unfold FullerData.nz HermDatum.nz
  rw [dif_pos hnz]
  exact key _ _ hnz.choose_spec.choose_spec

end GroundTheory.Heights₂.Heights.NineStatements
