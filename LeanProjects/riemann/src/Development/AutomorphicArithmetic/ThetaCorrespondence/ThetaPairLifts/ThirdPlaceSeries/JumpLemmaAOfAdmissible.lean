import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
theorem jumpLemma_a_of_admissible_alt_alt {L : SizeData₂ D} (hP : AdmPar L) (hG2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D) (hCr : CrysIffWD D.nd D.naut)
    (hG2g : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D) (hDi : AdmDict D) (hRd : AdmRead D) : ConclusionJa D := by
  obtain ⟨ep, hdict⟩ := hDi
  refine ⟨ep, ?_⟩
  intro i r hr w hw C τ
  obtain ⟨hInd, ⟨g, hg⟩, hread⟩ := hRd i r hr w hw C τ
  obtain ⟨ρ, hρ⟩ := exists_placeOf (D := D) g
  have hRA : ReadAt D i (gEmb C τ) g ρ := ⟨hg, hρ⟩
  obtain ⟨sg, cτ, hsU, hsD, hJ0, hchi⟩ := hdict i (gEmb C τ) g ρ hRA
  obtain ⟨hχdR, hχJ⟩ := hchi w hInd
  rw [Multiset.map_eq_singleton] at hχJ
  obtain ⟨c, hc, hcq⟩ := hχJ
  have hjr := D.nd.j_range i
  have hF := jFacts_of hP (D.nd.j i) hjr.1 hjr.2 ρ
  set up := decide (TypeU D ep g) with hup
  have hsU' : up = true → sg = 1 := fun h => hsU (by simpa [hup] using h)
  have hsD' : up = false → sg = -1 := fun h => hsD (by simpa [hup] using h)
  have hx : ∀ x, D.naut.IsdRW i (rQ D i r x) w ∧
      D.naut.jumpsW i (rQ D i r x) (gEmb C τ) = D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ) := by
    intro x
    by_cases hl : D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1
    · have h := _root_.UpperTheory.GalS.g2g' hG2g i r hr hl w hw x
      exact ⟨h.1, h.2 _ hInd⟩
    · push Not at hl
      have h := _root_.UpperTheory.GalS.g2a' (hG2 i r hr) w hw hl.1 hl.2 x
      have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      exact ⟨((hCr i _ _ w hw hcont).1 h.1).1, h.2 _ hInd⟩
  have hkey : ∀ a : ℤ, (((D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ)).count (a + c) : ℕ) : ℤ) =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 :=
    count_key hF _ sg cτ c up hsU' hsD' hJ0 hcq
  have hTw : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).1, (hx x).2, hkey]
  have hDu : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
      if (a : ℚ) ∈ dualS (JJ D up (D.nd.j i) ρ) then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).2, (hx x).2, dualS_int, ← hkey]
    congr 3; ring
  refine ⟨g, ρ, hRA, ?_, ?_⟩
  · intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    refine ⟨?_, hTw x a, ?_, hDu x a⟩
    · rw [h2 _ (Or.inl rfl) a, hTw x a]; exact ite_ne_zero_iff' _
    · rw [h2 _ (Or.inr rfl) a, hDu x a]; exact ite_ne_zero_iff' _
  · intro ρπ π hπ hdec a
    obtain ⟨h1, h2, h3⟩ := hread π (hx π).1 hχdR c hc
    have hW : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ JW D up (D.nd.j i) ρ then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).1, hTw π a]
      by_cases hb : (a : ℚ) ∈ blockJ D
      · have hb' := (block_mem_iff (D := D) a).1 hb
        rw [if_pos (block_sub_JJ up _ ρ _ hb), if_pos hb', if_neg (block_not_mem_JW hF up _ hb)]
        simp
      · have hb' : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hb ((block_mem_iff a).2 h)
        rw [if_neg hb', sub_zero]
        simp only [JJ_iff_JW hF up _ hb]
    have hT : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ dualS (JW D up (D.nd.j i) ρ) then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).2.1, hW, dualS_int]
    refine ⟨?_, hW a, ?_, hT a⟩
    · rw [(h3 ρπ hπ hdec a).2.2.1, hW a]; exact ite_ne_zero_iff' _
    · rw [(h3 ρπ hπ hdec a).2.2.2, hT a]; exact ite_ne_zero_iff' _
end GlobalTheory.JumpSets
end
end
