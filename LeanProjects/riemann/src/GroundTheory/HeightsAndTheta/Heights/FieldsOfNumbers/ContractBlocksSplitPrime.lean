import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HomFracDegZeroEqFunField
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.AddBlockVarEquivFst
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem PFDegree.toIndefiniteRowSideFullHecke (hA : ProjectionFormulaDegree.Statement.{u}) :
    IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} := by
  intro F _ K _ _ L _ _ ι _ ι₂ _ P' hP' n hc hP bs
  have : ∀ s, Fintype (Sum.elim ι ι₂ s) := fun s => match s with
    | .inl k => (inferInstance : Fintype (ι k))
    | .inr l => (inferInstance : Fintype (ι₂ l))
  obtain ⟨-, h⟩ := hA F K (K ⊕ L) Function.Embedding.inl (Sum.elim ι ι₂) P' hP' n
    ((relDim_eq_iff_hasRelDim P' n).mpr hP)
    ((relDim_eq_iff_hasRelDim (IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks ι₂ P') n).mpr hc) bs
  have := hP'.isPrime
  simp only [AddBlockFunctionField.pullDeg_inl, AddBlockFunctionField.relDeg_inl] at h
  exact h

section Split

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

def splitBlockEquiv : K ⊕ blockCompl j ≃ K' :=
  Equiv.ofBijective (Sum.elim j Subtype.val) (by
    refine ⟨?_, fun k' => ?_⟩
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (j.injective h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr ⟨k', h⟩, rfl⟩)

def splitVarEquiv : (Σ s, splitCoord j ι' s) ≃ (Σ k', ι' k') :=
  Equiv.ofBijective (splitVar j ι') (by
    refine ⟨?_, fun ⟨k', i⟩ => ?_⟩
    · rintro ⟨a | a, x⟩ ⟨b | b, y⟩ h
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases j.injective h1
        cases eq_of_heq h2
        rfl
      · exact absurd ⟨a, congrArg Sigma.fst h⟩ b.2
      · exact absurd ⟨b, (congrArg Sigma.fst h).symm⟩ a.2
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases Subtype.ext h1
        cases eq_of_heq h2
        rfl
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨⟨Sum.inl k, i⟩, rfl⟩
      · exact ⟨⟨Sum.inr ⟨k', h⟩, i⟩, rfl⟩)

theorem splitVarEquiv_fst (v : Σ s, splitCoord j ι' s) :
    (splitVarEquiv j ι' v).1 = splitBlockEquiv j v.1 := by
  rcases v with ⟨k | l, i⟩ <;> rfl

theorem contractBlocks_splitPrime {F : Type u} [Field F] (P' : Ideal (MRing ι' F)) :
    IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks (fun l : blockCompl j => ι' l.1) (splitPrime j P') =
      contractPrime j P' := by
  ext p
  unfold IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks splitPrime contractPrime IndefiniteRowSideFullHecke.FieldNumbers.blockIncl
  simp only [Ideal.mem_comap]
  have e : rename (splitVar j ι') (rename (fun x : Σ k, ι' (j k) =>
      (⟨Sum.inl x.1, x.2⟩ : Σ s, splitCoord j ι' s)) p) = rename (blockIncl j ι') p := by
    rw [rename_rename]
    rfl
  exact iff_of_eq (congrArg (· ∈ P') e)

theorem pullDeg_split (b : K → ℤ) :
    IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) b ∘ (splitBlockEquiv j).symm = pullDeg j b := by
  funext k'
  obtain ⟨s, rfl⟩ := (splitBlockEquiv j).surjective k'
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases s with k | l
  · exact (j.injective.extend_apply b 0 k).symm
  · show (0 : ℤ) = Function.extend j b 0 l.1
    rw [Function.extend_apply' _ _ _ (fun h => l.2 h)]
    rfl

theorem relDim_splitPrime {F : Type u} [Field F] [Fintype K] [Fintype K'] [Fintype (blockCompl j)]
    (P' : Ideal (MRing ι' F)) : relDim (splitPrime j P') = relDim P' := by
  have e : MRing (splitCoord j ι') F ⧸ splitPrime j P' ≃+* MRing ι' F ⧸ P' :=
    Ideal.quotientEquiv _ _ (renameEquiv F (splitVarEquiv j ι')).toRingEquiv
      (Ideal.map_comap_of_surjective _ (renameEquiv F (splitVarEquiv j ι')).surjective P').symm
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv e, Fintype.card_congr (splitBlockEquiv j)]

end Split

theorem contract_funField_le (h₁ : RenameMultiHomog.Statement.{u}) {F : Type u} [Field F]
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨Function.extend j d 0, rename (blockIncl j ι') f,
    rename (blockIncl j ι') g, h₁ F K K' j _ ι' _ (fun _ => rfl) f d hf,
    h₁ F K K' j _ ι' _ (fun _ => rfl) g d hg, hgP, ?_⟩
  simp [contractFracMap, contractQuot, map_div₀]
  rfl

theorem PFDegree.split_model_to_place_model (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) (hB : IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0}) :
    ProjectionFormulaDegree.Statement.{u} := by
  classical
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP hc bs
  have := hP'.isPrime
  refine ⟨contract_funField_le h₁ j P', ?_⟩
  have hQ : IsMultiProjPrime (splitPrime j P') :=
    h₃ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' hP'
  have h := hB F K (blockCompl j) (fun k => ι' (j k)) (fun l => ι' l.1) (splitPrime j P') hQ n
    (by
      rw [contractBlocks_splitPrime]
      exact (relDim_eq_iff_hasRelDim _ n).mp hc)
    (by
      refine (relDim_eq_iff_hasRelDim _ n).mp ?_
      rw [relDim_splitPrime]
      exact hP) bs
  rw [← AddBlockFunctionField.relDeg_inl, ← h₄, contractBlocks_splitPrime] at h
  rw [← h]
  have h2 := h₂ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' n
    (fun i => IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) (bs i))
  simp only [pullDeg_split] at h2
  exact h2.symm

theorem PFDegree.equiv (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} ↔ IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} :=
  ⟨PFDegree.toIndefiniteRowSideFullHecke, PFDegree.split_model_to_place_model h₁ h₂ h₃ h₄⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
