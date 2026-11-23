import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem gP_kP {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (x : K) : gP l g (kP l K x) = kP l K x := by
  have h1 : (toBot g.1) • algClToBdR l (K.val x) = algClToBdR l ((toBot g.1) (K.val x)) :=
    gal_smul_algClToBdR _ _
  have h2 : (toBot g.1) (K.val x) = K.val x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
  rw [h2] at h1
  exact h1

theorem sigA_fix : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  intro l _ K M h k g a
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  show Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = _
  rw [Ideal.quotientMap_mk, gP_kP]
  rfl

end GlobalTheory.CompanionTheory.LatC
