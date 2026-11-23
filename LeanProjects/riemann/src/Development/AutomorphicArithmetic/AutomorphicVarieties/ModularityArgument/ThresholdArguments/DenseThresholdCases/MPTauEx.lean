import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PTauEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KapEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuDefsA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)
theorem tauEx' (h1 : _root_.UpperTheory.V.Cu2.KapExAlt) (h2 : TauOf) : _root_.UpperTheory.V.Cu.TauExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK hTC hdisc hdec hcc g0 hg0
  obtain ⟨m, κ, hκ⟩ := h1 hP Ω l ι K' hl2 hK hTC hdisc hdec hcc
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  haveI : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  haveI : T2Space (G K' Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[K'] Ω))
  have hc : Continuous κ := by simpa using (hκ 1 le_rfl).cont
  obtain ⟨E, hE, hmE⟩ := ce_char (G K' Ω) κ hc
  haveI := hE
  obtain ⟨c₁, hc₁⟩ := UpperTheory.V.X.So.coefOf l E
  refine ⟨m, c₁, κ, fun c₂ hc₂ j hj => ?_⟩
  refine h2 Ω l ι K' hl2 hK hdec g0 hg0 (m * j) (κ ^ j) (hκ j hj) c₂ fun h => ?_
  have e : (((κ ^ j) h : (Qbar l)ˣ) : Qbar l) = ((κ h : (Qbar l)ˣ) : Qbar l) ^ j := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  rw [e]
  exact pow_mem (hc₂ ((hc₁ _).2 (hmE h))) j
end UpperTheory.V.Cu2
end
end
