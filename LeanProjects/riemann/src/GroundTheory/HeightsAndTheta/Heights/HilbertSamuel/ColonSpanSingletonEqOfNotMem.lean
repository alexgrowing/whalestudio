import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

theorem ringKrullDim_quot_add_one_le {K : Type*} {ι : K → Type*} {F : Type*} [Field F]
    {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfQ

theorem le_of_add_one_le_natCast_add_one {x : WithBot ℕ∞} {n : ℕ}
    (h : x + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast h
      rw [top_add, WithBot.coe_le_coe] at h'
      exact absurd h' (by simp)
    | coe m =>
      have h' : (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      have h'' : m + 1 ≤ n + 1 := by exact_mod_cast WithBot.coe_le_coe.mp h'
      have : m ≤ n := by omega
      exact_mod_cast this

theorem colon_span_singleton_eq_of_not_mem {R : Type*} [CommRing R] {q : Ideal R} [q.IsPrime]
    {s : R} (hs : s ∉ q) : q.colon (Ideal.span {s}) = q := by
  ext x
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
  constructor
  · intro h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_right hs
  · intro h
    exact q.mul_mem_right _ h

theorem HilbertIncrement.closed : HilbertIncrement.Statement.{u} := by
  intro F _ K _ _ ι _ d q b i hq hdim hd hX
  have : q.IsPrime := hq.isPrime
  refine ⟨fun a => ?_, fun W _ hle => ?_⟩
  · have hhom : IsMultiHomog (X ⟨b, i⟩ : MRing ι F) (Pi.single b 1) :=
      isWeightedHomogeneous_X F (blockWeight ι) ⟨b, i⟩
    have h := HilbExactDivide.closed F K ι q hq.multiHomog (Pi.single b 1) (X ⟨b, i⟩) hhom a
    have hcast : (a - fun k => (((Pi.single b 1 : K → ℕ) k : ℕ) : ℤ)) = a - Pi.single b 1 := by
      funext k
      by_cases hk : k = b
      · subst hk
        simp
      · simp [Pi.single_apply, hk]
    rwa [colon_span_singleton_eq_of_not_mem hX, hcast] at h
  · have hXW : (X ⟨b, i⟩ : MRing ι F) ∈ W :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hstep := ringKrullDim_quot_add_one_le (le_sup_left.trans hle) hX hXW
    rw [hdim] at hstep
    have hn : d + Fintype.card K = (d - 1 + Fintype.card K) + 1 := by omega
    rw [hn] at hstep
    exact le_of_add_one_le_natCast_add_one hstep

theorem HilbertIncrement.hilbertIncrement_alt_of_statement :
    _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement.Statement.{u} →
      HilbertIncrement.Statement.{u} :=
  fun _ => HilbertIncrement.closed

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
