import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.Proof.LocalGlobalAssembly

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GlobalTheory.PtCore.GoodPtRow D := by
  intro D _ _ hZ a π hπ
  have hπ' : π ∈ ZgoodN D.nd D.naut a := (D.Zgood_tie a π).1 hπ
  obtain ⟨-, Sig, hX, hg⟩ := id hπ'
  have hHG : HG D.nd D.naut a := ⟨π, hπ'⟩
  have h1 := ((hZ a hHG).1 π hπ' Sig hX).2

  have hE : eigC D.nd D.naut a π ≠ ⊥ := by
    obtain ⟨P, hP, -⟩ := hX
    intro h
    apply D.naut.typeV_ne a P
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | D.naut.ptV a P = some π}) => D.naut.typeV a P) P hP le_rfl
  have hM : MjSig D.nd D.naut a Sig ≠ ⊥ := by
    intro h
    apply hE
    rw [← h1, h, Submodule.map_bot]
  obtain ⟨σ, hW, hσ⟩ : ∃ σ, HasParamW D.nd D.naut a σ Sig ∧ D.what₂.isot (D.nd.j a) σ ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    apply hM
    unfold MjSig
    exact le_bot_iff.1 (iSup₂_le fun σ hW => (hc σ hW).le)
  have hgr : D.nd.goodRow σ := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW.2.2).2 hg
  exact ⟨σ, Sig, ⟨hgr, hσ⟩, hW, hX⟩

end GlobalTheory.Proof.LocalGlobalAssembly
