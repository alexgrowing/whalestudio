import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_gB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (x : Bk l (k + 1)) :
    dk l k (gB h (k + 1) g x) = gB h k g (dk l k x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [dk, gB, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

theorem levSys_dA_σA {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g a,
    (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  intro m g a
  apply Subtype.ext
  exact dk_gB h (m + 1) g a.1

end GlobalTheory.CompanionTheory.LatLevel
