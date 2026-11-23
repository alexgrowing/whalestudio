import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem toB_on_K : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  intro l _ K M h k a y hy
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) := fun x y h =>
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h
  have key : pInv l y = kP l K a := by
    apply hinj
    have h1 : algebraMap (BdRp l) (BdR l) (pInv l y) = y.1 := by
      have := (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply y
      exact congrArg Subtype.val this
    rw [h1]
    exact hy
  show pk l k (pInv l y) = pk l k (kP l K a)
  rw [key]

end GlobalTheory.CompanionTheory.LatC
