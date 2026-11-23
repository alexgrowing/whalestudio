import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractBlocksSplitPrime
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section SplitRelDeg

variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]

def splitQuotToFrac :
    (MRing (splitCoord j ι') F ⧸ splitPrime j P') →ₐ[F] FractionRing (MRing ι' F ⧸ P') :=
  (IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
    (Ideal.quotientMapₐ P' (rename (splitVar j ι')) le_rfl)

def splitFracMap :
    FractionRing (MRing (splitCoord j ι') F ⧸ splitPrime j P') →ₐ[F]
      FractionRing (MRing ι' F ⧸ P') :=
  IsFractionRing.liftAlgHom (g := splitQuotToFrac j P')
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective)

theorem splitFracMap_mk (f : MRing (splitCoord j ι') F) :
    splitFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (splitPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (splitVar j ι') f)) := by
  simp [splitFracMap, splitQuotToFrac]
  rfl

theorem contractFracMap_mk (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl

theorem rename_splitVar_blockIncl_inl {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Σ k, ι' (j k)) R) :
    rename (splitVar j ι')
        (rename (blockIncl (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitCoord j ι')) f) =
      rename (blockIncl j ι') f :=
  (rename_rename _ _ f).trans rfl

theorem rename_splitVar_symm {R : Type*} [CommSemiring R] (f : MvPolynomial (Σ k', ι' k') R) :
    rename (splitVar j ι') (rename (splitVarEquiv j ι').symm f) = f := by
  show rename (splitVarEquiv j ι') (rename (splitVarEquiv j ι').symm f) = f
  rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]

theorem extend_equiv_zero {A B : Type} (E : A ≃ B) (d : A → ℕ) :
    Function.extend E d 0 = d ∘ E.symm := by
  funext b
  obtain ⟨a, rfl⟩ := E.surjective b
  simp [E.injective.extend_apply]

omit [P'.IsPrime] in
theorem mem_contractPrime_inl_iff (g : MRing (fun k => ι' (j k)) F) :
    g ∈ contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P') ↔
      g ∈ contractPrime j P' :=
  iff_of_eq (congrArg (· ∈ P') (rename_splitVar_blockIncl_inl j g))

theorem splitFracMap_contractFracMap_inl_mk (f : MRing (fun k => ι' (j k)) F) :
    splitFracMap j P' (contractFracMap (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P') (algebraMap _ _
          (Ideal.Quotient.mk (contractPrime Function.Embedding.inl (splitPrime j P')) f))) =
      contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) := by
  have h1 := contractFracMap_mk (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P') f
  have h2 := splitFracMap_mk j P' (rename (blockIncl Function.Embedding.inl (splitCoord j ι')) f)
  have h3 := contractFracMap_mk j P' f
  have h4 := rename_splitVar_blockIncl_inl j (R := F) f
  exact (congrArg (splitFracMap j P') h1).trans (h2.trans ((congrArg (fun p =>
    algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' p)) h4).trans
      h3.symm))

theorem map_splitFracMap_homFracDegZero [DecidableEq K] [DecidableEq K'] :
    (homFracDegZero (splitPrime j P')).map (splitFracMap j P') = homFracDegZero P' := by
  set E := splitBlockEquiv j
  set σ := splitVarEquiv j ι'
  have hσ : ∀ v, (σ v).1 = E v.1 := splitVarEquiv_fst j ι'
  have hσ' : ∀ v, (σ.symm v).1 = E.symm v.1 := fun v => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgQ, rfl⟩, rfl⟩
    refine ⟨b ∘ E.symm, rename (splitVar j ι') f, rename (splitVar j ι') g, ?_, ?_, hgQ, ?_⟩
    · have := RenameMultiHomog.proof F _ K' E.toEmbedding _ ι' σ hσ f b hf
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero] at this
    · have := RenameMultiHomog.proof F _ K' E.toEmbedding _ ι' σ hσ g b hg
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero] at this
    · rw [map_div₀, splitFracMap_mk, splitFracMap_mk]
  · rintro ⟨b, f, g, hf, hg, hgP, rfl⟩
    refine ⟨_, ⟨b ∘ E, rename σ.symm f, rename σ.symm g, ?_, ?_, ?_, rfl⟩, ?_⟩
    · have := RenameMultiHomog.proof F K' _ E.symm.toEmbedding ι' _ σ.symm hσ' f b hf
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero, Equiv.symm_symm] at this
    · have := RenameMultiHomog.proof F K' _ E.symm.toEmbedding ι' _ σ.symm hσ' g b hg
      rwa [Equiv.coe_toEmbedding, extend_equiv_zero, Equiv.symm_symm] at this
    · show rename (splitVar j ι') (rename σ.symm g) ∉ P'
      rwa [rename_splitVar_symm]
    · rw [map_div₀, splitFracMap_mk, splitFracMap_mk, rename_splitVar_symm, rename_splitVar_symm]

theorem map_splitFracMap_contract [DecidableEq K] [DecidableEq K'] :
    ((homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P'))).map (contractFracMap Function.Embedding.inl (splitPrime j P'))).map
        (splitFracMap j P') =
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
  rw [IntermediateField.map_map]
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgQ, rfl⟩, rfl⟩
    refine ⟨_, ⟨b, f, g, hf, hg, ?_, rfl⟩, ?_⟩
    · exact fun h => hgQ ((mem_contractPrime_inl_iff j P' g).mpr h)
    · simp only [AlgHom.comp_apply, map_div₀]
      exact (congrArg₂ (· / ·) (splitFracMap_contractFracMap_inl_mk j P' f)
        (splitFracMap_contractFracMap_inl_mk j P' g)).symm
  · rintro ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    refine ⟨_, ⟨b, f, g, hf, hg, ?_, rfl⟩, ?_⟩
    · exact fun h => hgP ((mem_contractPrime_inl_iff j P' g).mp h)
    · simp only [AlgHom.comp_apply, map_div₀]
      exact congrArg₂ (· / ·) (splitFracMap_contractFracMap_inl_mk j P' f)
        (splitFracMap_contractFracMap_inl_mk j P' g)

end SplitRelDeg

theorem SplitRelDeg.proof : SplitRelDeg.Statement.{u} := by
  intro F _ K K' _ _ j ι' P' _
  unfold relDeg
  have h := IntermediateField.relfinrank_map_map
    ((homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P'))).map (contractFracMap Function.Embedding.inl (splitPrime j P')))
    (homFracDegZero (splitPrime j P')) (splitFracMap j P')
  rw [map_splitFracMap_contract, map_splitFracMap_homFracDegZero] at h
  exact h

end

end GroundTheory.Heights₂.Heights.FieldNumbers
