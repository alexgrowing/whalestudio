import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.LSeq

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem lpow_nzd (n : ℕ) : (l : A.Acr0) ^ n ∈ nonZeroDivisors A.Acr0 :=
  pow_mem (A.acris_torsion_free l (Fact.out : l.Prime).ne_zero) n

set_option synthInstance.maxHeartbeats 400000 in

def alphaL (n : ℕ) : A.Acr0 →ₗ[A.Acr0] (A.Acr0 ⧸ Ideal.span {(l : A.Acr0) ^ (n + 1)}) :=
  (Submodule.mkQ _).comp (LinearMap.mulLeft A.Acr0 ((l : A.Acr0) ^ n))

set_option synthInstance.maxHeartbeats 400000 in

def alpha (n : ℕ) : A.Acr 1 →+ A.Acr (n + 1) :=
  ((Ideal.span {(l : A.Acr0) ^ 1}).liftQ (alphaL A n) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker]
    simp only [alphaL, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩)).toAddMonoidHom

theorem alpha_mk (n : ℕ) (y : A.Acr0) :
    alpha A n (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y) := rfl

theorem alpha_injective (n : ℕ) : Function.Injective (alpha A n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr 1 y = x := Ideal.Quotient.mk_surjective x
  rw [alpha_mk] at hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have h0 : (l : A.Acr0) ^ n * (y - c * (l : A.Acr0) ^ 1) = 0 := by
    rw [mul_sub, ← hc]; ring
  have h1 := mem_nonZeroDivisors_iff_left.1 (lpow_nzd A n) _ h0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, (sub_eq_zero.1 h1).symm⟩)

theorem alpha_exact (n : ℕ) : Function.Exact (alpha A n) (A.red n.le_succ) := by
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, A.mkAcr (n + 1) y = x := Ideal.Quotient.mk_surjective x
  rw [red_mk]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact ⟨A.mkAcr 1 c, by rw [alpha_mk, ← hc, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ : ∃ w, A.mkAcr 1 w = z := Ideal.Quotient.mk_surjective z
    rw [← red_mk A n.le_succ y, ← hz, alpha_mk, red_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨w, mul_comm _ _⟩)

theorem racrSeq (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcrSeq l :=
  fun n => ⟨fun A => alpha A n, fun A y => alpha_mk A n y, fun A => ⟨alpha_injective A n, alpha_exact A n⟩⟩

end GlobalTheory.CompanionTheory.LSeq
