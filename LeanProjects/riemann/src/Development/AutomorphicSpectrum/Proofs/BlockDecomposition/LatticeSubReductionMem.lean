import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_fk (l : ℕ) [Fact l.Prime] (k : ℕ) (w : Ainf l) :
    Lat.dk l k (Lat.fk l (k + 1) w) = Lat.fk l k w := by
  simp only [Lat.dk, Lat.fk, RingHom.comp_apply]
  exact Ideal.Quotient.factor_mk _ _

theorem dk_dpE (l : ℕ) [Fact l.Prime] (M k i : ℕ) :
    Lat.dk l k (Lat.dpE (Lat.fk l (k + 1)) (xi0 l) l M i) = Lat.dpE (Lat.fk l k) (xi0 l) l M i := by
  simp only [Lat.dpE, Lat.η, map_rat_smul, map_pow, dk_fk]

theorem dk_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) :
    ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro x hx
  have hle : Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M ≤
      (Lat.sub (Lat.fk l k) (xi0 l) l M).comap (Lat.dk l k) := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_fk]
      exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_dpE]
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  exact hle hx

end GlobalTheory.CompanionTheory.LatLevel
