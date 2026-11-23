import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_toB_ker {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  have ht : (per l K).tB = algebraMap (BdRp l) (BdR l) (tBdR l) := by
    change DeRhamPotentiallySemistable.DRPst.iC l (tA l) = _
    change algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
    rw [show ACris.iota ℂ_[l] l (tA l) = tBdR l from ACris.iota_periodT (untilt_epsilon (p := l))]
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  have hp : ∀ x : ↥(algebraMap (BdRp l) (BdR l)).range, algebraMap (BdRp l) (BdR l) (pInv l x) = x := by
    intro x
    obtain ⟨z, hz⟩ := x.2
    have : pInv l x = z := by
      apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_eq.2
      exact Subtype.ext hz.symm
    rw [this, hz]
  intro x
  change pk l k (pInv l x) = 0 ↔ _
  rw [pk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨algebraMap (BdRp l) (BdR l) z, z, rfl⟩, ?_⟩
    have := hp x
    rw [← hz, map_mul, map_pow, mul_comm] at this
    rw [ht]
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, hinj ?_⟩
    rw [map_mul, map_pow, mul_comm, hp x, hz]
    rw [ht] at hy
    exact hy.symm

end GlobalTheory.CompanionTheory.LatC
