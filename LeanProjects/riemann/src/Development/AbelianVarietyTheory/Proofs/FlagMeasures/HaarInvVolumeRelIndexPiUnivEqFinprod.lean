import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem invVol_pi_univ : ∀ {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (K U : ∀ i, Subgroup (G i)),
    {i | K i ≠ U i}.Finite → (∀ i, (K i).relIndex (U i) ≠ 0 ∧ (U i).relIndex (K i) ≠ 0) →
    (Subgroup.pi Set.univ K).relIndex (Subgroup.pi Set.univ U) ≠ 0 ∧
    (Subgroup.pi Set.univ U).relIndex (Subgroup.pi Set.univ K) ≠ 0 ∧
    invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) = ∏ᶠ i, invVol (K i) (U i) := by
  intro ι G _ K U hfin hne
  classical
  set S := hfin.toFinset with hSdef
  have hoff : ∀ i, i ∉ S → K i = U i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have key : ∀ A B : ∀ i, Subgroup (G i), (∀ i, i ∉ S → A i ≤ B i) →
      (Subgroup.pi Set.univ B).relIndex (Subgroup.pi Set.univ A) =
        ∏ i ∈ S, (B i).relIndex (A i) := by
    intro A B hAB
    exact GlobalTheory.relIndex_eq_prod_local (∀ i, G i) ι G (fun i => Pi.evalMonoidHom G i) ⊤
      (Subgroup.pi Set.univ A) (Subgroup.pi Set.univ B) A B S
      (fun v h _ => ⟨Pi.mulSingle v h, Subgroup.mem_top _, by simp,
        fun w hw => by simp [Pi.mulSingle_eq_of_ne hw]⟩)
      (fun g => by simp [Subgroup.mem_pi])
      (fun g => by simp [Subgroup.mem_pi])
      hAB
  have h1 := key K U (fun i hi => (hoff i hi).le)
  have h2 := key U K (fun i hi => (hoff i hi).ge)
  have hfp : ∀ f : ι → ℝ, (∀ i, i ∉ S → f i = 1) → ∏ᶠ i, f i = ∏ i ∈ S, f i := fun f hf =>
    finprod_eq_prod_of_mulSupport_subset f (fun i hi => by
      by_contra h
      exact hi (hf i h))
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).1)
  · rw [h1]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).2)
  · rw [hfp _ (fun i hi => by simp [invVol, hoff i hi, Subgroup.relIndex_self])]
    simp only [invVol, h1, h2, Nat.cast_prod]
    rw [Finset.prod_div_distrib]

end GlobalTheory.HL
