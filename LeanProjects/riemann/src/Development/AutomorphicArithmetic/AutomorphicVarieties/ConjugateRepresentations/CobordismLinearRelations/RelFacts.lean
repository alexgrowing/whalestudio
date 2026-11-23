import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelKer
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem oc_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U U' : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (h3 : IsOpen (U' : Set G)) :
    IsOpen ((U ⊓ U' : Subgroup G) : Set G) ∧ IsCompact ((U ⊓ U' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact ⟨h1.inter h3, h2.inter_right (U'.isClosed_of_isOpen h3)⟩

private theorem oc_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x⁻¹ * u * x) ⁻¹' U := by
      ext u; simp
    rw [this]
    exact h1.preimage (by fun_prop)
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x * u * x⁻¹) '' U := by
      ext u
      constructor
      · intro hu
        exact ⟨x⁻¹ * u * x, by simpa using hu, by group⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [mul_assoc] using hv
    rw [this]
    exact h2.image (by fun_prop)

theorem UpperTheory.V.Cj.relFacts :
    UpperTheory.V.Cj.RelFacts := by
  intro E _ _ _ a ha σ Ξ Ξ' h hσ q
  have mono : ∀ U U' : Subgroup (GL (Fin a) (Af E)), U' ≤ U → ∀ (α : Co Ξ q) (β : Co Ξ' q),
      RelAt U σ h α β → RelAt U' σ h α β := fun U U' hU α β hr => by
    have := relPull E a U U' 1 (fun u hu => by simpa using hU hu) σ Ξ Ξ' h q α β hr
    rwa [trans_one, trans_one] at this
  have L := (levSub E a Ξ q).2.1
  have L' := (levSub E a Ξ' q).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s α α' β β' ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    exact ⟨U ⊓ V, w1, w2, relLin E a _ σ Ξ Ξ' h q s α α' β β' (mono _ _ inf_le_left _ _ u3) (mono _ _ inf_le_right _ _ v3)⟩
  · rintro x α β ⟨U, u1, u2, u3⟩
    obtain ⟨V, v1, v2, v3⟩ := oc_conj u1 u2 x
    exact ⟨V, v1, v2, relPull E a U V x v3 σ Ξ Ξ' h q α β u3⟩
  · rintro α β ⟨U, u1, u2, u3⟩
    constructor
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).1
        ((L _ _ inf_le_right α).2 v3)⟩
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).2
        ((L' _ _ inf_le_right β).2 v3)⟩
  · rintro α β ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩ d1 d2 ⟨X, x1, -, x3⟩ ⟨Y, y1, -, y3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    obtain ⟨w3, w4⟩ := oc_inf w1 w2 x1
    obtain ⟨w5, w6⟩ := oc_inf w3 w4 y1
    exact ⟨_, w5, w6, (relKer E a ha _ w6 σ Ξ Ξ' h hσ q α β).2
      ((L _ _ (inf_le_left.trans (inf_le_left.trans inf_le_left)) α).1 u3)
      ((L' _ _ (inf_le_left.trans (inf_le_left.trans inf_le_right)) β).1 v3) d1 d2
      ((L _ _ (inf_le_left.trans inf_le_right) α).2 x3) ((L' _ _ inf_le_right β).2 y3)⟩
