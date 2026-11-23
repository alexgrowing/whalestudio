import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem isSSRep_comp_subtype_of_normal_finiteIndex :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (a : ℕ) (ρ : Γ →* GL (Fin a) k)
      (N : Subgroup Γ), N.Normal → N.FiniteIndex → IsSSRep ρ → IsSSRep (ρ.comp N.subtype) := by
  intro Γ k _ _ _ a ρ N hN hfin hρ
  let M : Γ → Matrix (Fin a) (Fin a) k := fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  have hMmul : ∀ g h, M g * M h = M (g * h) := fun g h => by simp [M]
  have hMone : M 1 = 1 := by simp [M]
  have hMinv : ∀ g, M g⁻¹ * M g = 1 := fun g => by rw [hMmul, inv_mul_cancel, hMone]
  let S : Submodule k (Matrix (Fin a) (Fin a) k) :=
    Submodule.span k (Set.range fun n : N => M (n : Γ))
  have hSgen : ∀ n ∈ N, M n ∈ S := fun n hn => Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
  have hSmul : ∀ y ∈ S, ∀ z ∈ S, y * z ∈ S := by
    intro y hy z hz
    have h := Submodule.mul_mem_mul hy hz
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨n, rfl⟩, _, ⟨n', rfl⟩, rfl⟩
    exact ⟨n * n', (hMmul _ _).symm⟩
  have hSconj : ∀ g : Γ, ∀ y ∈ S, M g * y * M g⁻¹ ∈ S := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      rw [hMmul, hMmul]
      exact hSgen _ (hN.conj_mem _ n.2 g)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, add_mul]; exact S.add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc]; exact S.smul_mem c hy
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  change x ∈ S at hx
  change ∀ n : N, (x * M n).trace = 0 at htr

  let I : Set (Matrix (Fin a) (Fin a) k) := {z | z ∈ S ∧ ∀ y ∈ S, (z * y).trace = 0}
  have hxI : x ∈ I := by
    refine ⟨hx, fun y hy => ?_⟩
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨n, rfl⟩ := hy; exact htr n
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul c y _ hy => rw [mul_smul_comm, Matrix.trace_smul, hy, smul_zero]
  have hIr : ∀ z ∈ I, ∀ y ∈ S, z * y ∈ I := fun z hz y hy =>
    ⟨hSmul z hz.1 y hy, fun w hw => by rw [mul_assoc]; exact hz.2 _ (hSmul y hy w hw)⟩
  have hIconj : ∀ g : Γ, ∀ z ∈ I, M g * z * M g⁻¹ ∈ I := by
    intro g z hz
    refine ⟨hSconj g z hz.1, fun y hy => ?_⟩
    have hy' : M g⁻¹ * y * M g⁻¹⁻¹ ∈ S := hSconj g⁻¹ y hy
    rw [inv_inv] at hy'
    have e : (M g * z * M g⁻¹ * y).trace = (z * (M g⁻¹ * y * M g)).trace := by
      rw [mul_assoc, mul_assoc, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    rw [e]
    exact hz.2 _ hy'
  have hpow : ∀ g : Γ, ∀ j : ℕ, ∃ y ∈ I, (x * M g) ^ (j + 1) = y * M (g ^ (j + 1)) := by
    intro g j
    induction j with
    | zero => exact ⟨x, hxI, by simp⟩
    | succ j ih =>
      obtain ⟨y, hy, e⟩ := ih
      refine ⟨y * (M (g ^ (j + 1)) * x * M (g ^ (j + 1))⁻¹),
        hIr y hy _ (hIconj _ x hxI).1, ?_⟩
      rw [pow_succ (x * M g) (j + 1), e, pow_succ g (j + 1), ← hMmul (g ^ (j + 1)) g]
      have h1 := hMinv (g ^ (j + 1))
      calc y * M (g ^ (j + 1)) * (x * M g)
          = y * M (g ^ (j + 1)) * x * (M (g ^ (j + 1))⁻¹ * M (g ^ (j + 1))) * M g := by
            rw [h1]; simp only [mul_one, mul_assoc]
        _ = y * (M (g ^ (j + 1)) * x * M (g ^ (j + 1))⁻¹) * (M (g ^ (j + 1)) * M g) := by
            simp only [mul_assoc]
  have hm : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have htrΓ : ∀ g : Γ, (x * M g).trace = 0 := by
    intro g
    have hgm : g ^ N.index ∈ N := Subgroup.pow_index_mem N g
    have hnil : IsNilpotent ((x * M g) ^ N.index) := by
      apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
      intro e he _
      obtain ⟨y, hy, hye⟩ := hpow g (N.index * e - 1)
      have h1 : N.index * e - 1 + 1 = N.index * e := by
        have : 1 ≤ N.index * e := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (by omega))
        omega
      rw [h1] at hye
      rw [← pow_mul, hye]
      refine hy.2 _ (hSgen _ ?_)
      rw [pow_mul]
      exact N.pow_mem hgm e
    obtain ⟨e, he⟩ := hnil
    have hnil' : IsNilpotent (x * M g) := ⟨N.index * e, by rw [pow_mul, he]⟩
    exact (Matrix.isNilpotent_trace_of_isNilpotent hnil').eq_zero
  have hxΓ : x ∈ spanAlg ρ := by
    rw [mem_spanAlg]
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  exact trace_nondegenerate_of_isSSRep ρ hρ x hxΓ htrΓ

end GlobalTheory.TraceSemisimple
