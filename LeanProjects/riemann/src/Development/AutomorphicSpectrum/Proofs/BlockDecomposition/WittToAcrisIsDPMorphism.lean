import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisDP

theorem wn_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ),
    IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  intro l _ K r n
  let F₀ : WittVector l r.k →+* (base l).Acr0 :=
    (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))
  refine RL.pd_mor (Ideal.Quotient.mk _) ((base l).mkAcr n) (Ideal.span {(l : WittVector l r.k)}) (base l).PFil0
    (Wc.pd l r.k n) (B.DD true (base l) n) F₀ (Mid.wn r n) Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) ((base l).isPd_pdPFil n) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  · intro a
    rw [Mid.wn_mk]
    exact (base l).cris_algebraMap n (WittVector.map r.s a)

end GlobalTheory.CompanionTheory.CrisDP
