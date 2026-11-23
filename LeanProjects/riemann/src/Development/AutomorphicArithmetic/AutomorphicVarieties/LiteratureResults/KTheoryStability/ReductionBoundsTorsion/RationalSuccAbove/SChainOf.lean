import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.RatSuccAboveSucc

noncomputable section

namespace PositivityTheory.KB

theorem sChain_of : SChain := by
  have hbd : ∀ (G : Type) [Group G] (m : ℕ), bd G m = SimplicialChains.ibd G m := fun _ _ _ => rfl
  have hcm : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ), cmap f m = SimplicialChains.icmap f m :=
    fun _ _ _ _ _ _ => rfl
  refine ⟨fun G _ m z => ?_, fun G H _ _ f m z => ?_, fun G H K _ _ _ f g m z => ?_,
    fun G _ g m z hz => ?_⟩
  · rw [hbd, hbd]
    exact SimplicialChains.ibd_ibd m z
  · rw [hbd, hbd, hcm, hcm]
    exact SimplicialChains.ibd_icmap f m z
  · rw [hcm, hcm, hcm]
    exact SimplicialChains.icmap_comp f g m z
  · unfold IsBd
    unfold IsCyc at hz
    rw [hbd] at hz ⊢
    rw [hcm]
    exact SimplicialChains.conj_bd g m z hz

end PositivityTheory.KB
