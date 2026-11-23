import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem pInv_algebraMap (l : ℕ) [Fact l.Prime] (b : BdRp l) (hb : algebraMap (BdRp l) (BdR l) b ∈ (algebraMap (BdRp l) (BdR l)).range) :
    pInv l ⟨algebraMap (BdRp l) (BdR l) b, hb⟩ = b := by
  have : (⟨algebraMap (BdRp l) (BdR l) b, hb⟩ : ↥(algebraMap (BdRp l) (BdR l)).range) = (algebraMap (BdRp l) (BdR l)).rangeRestrict b := rfl
  rw [this]
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply b

theorem sigmaB_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y →
      (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  rintro g ⟨_, b, rfl⟩ ⟨y, hy⟩ hxy
  have hy' : y = algebraMap (BdRp l) (BdR l) (gP l g b) := by
    refine (Eq.trans hxy.symm ?_)
    exact galBdRField_algebraMap (toBot g.1) b
  subst hy'
  show gB h k g (pk l k (pInv l ⟨_, _⟩)) = pk l k (pInv l ⟨_, _⟩)
  rw [pInv_algebraMap, pInv_algebraMap]
  rfl

end GlobalTheory.CompanionTheory.LatC
