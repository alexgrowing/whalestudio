import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WittHighPow

theorem high_pow_coeff_mem_span_pow :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p] (x : WittVector p R) (N m : ℕ), ∃ k : ℕ, ∀ (z : WittVector p R) (n : ℕ), n < N → (x ^ k * z).coeff n ∈ Ideal.span {x.coeff 0 ^ m} := by
  intro p _ R _ _ _ x N m
  classical
  set J : Ideal R := Ideal.span {x.coeff 0 ^ m} with hJ
  let f : WittVector p R →+* TruncatedWittVector p N (R ⧸ J) :=
    (WittVector.truncate N).comp (WittVector.map (Ideal.Quotient.mk J))
  have hmem : ∀ w : WittVector p R, w ∈ RingHom.ker f ↔ ∀ n < N, w.coeff n ∈ J := by
    intro w
    rw [RingHom.mem_ker]
    constructor
    · intro h n hn
      have := congrArg (fun t => TruncatedWittVector.coeff ⟨n, hn⟩ t) h
      simp only [f, RingHom.comp_apply, WittVector.coeff_truncate,
        WittVector.map_coeff, TruncatedWittVector.coeff_zero] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).1 this
    · intro h
      ext i
      simp only [f, RingHom.comp_apply, WittVector.coeff_truncate,
        WittVector.map_coeff, TruncatedWittVector.coeff_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (h i i.2)
  set I := RingHom.ker f
  set ϖ := x.coeff 0
  set t : WittVector p R := WittVector.teichmuller p ϖ
  set y : WittVector p R := x - t
  have hy0 : y.coeff 0 = 0 := by
    have h1 : x = y + t := by simp [y]
    have h2 := congrArg (fun w => w.coeff 0) h1
    simp only [WittVector.add_coeff_zero, t, WittVector.teichmuller_coeff_zero] at h2
    linear_combination -h2
  have hyV : y = WittVector.verschiebung (y.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (by
      intro i hi; interval_cases i; exact hy0)
    simpa using this
  let u : WittVector p R := WittVector.mk p (fun n => (frobeniusEquiv R p).symm ((y.shift 1).coeff n))
  have hu : WittVector.frobenius u = y.shift 1 := by
    ext n
    rw [WittVector.coeff_frobenius_charP]
    simp only [u, WittVector.coeff_mk]
    exact frobenius_apply_frobeniusEquiv_symm R p _
  have hyp : y = u * (p : WittVector p R) := by
    rw [hyV, ← hu, WittVector.verschiebung_frobenius]
  have hx : x = t + u * (p : WittVector p R) := by
    rw [← hyp]; simp [y]
  have ht : t ^ m ∈ I := by
    rw [hmem]
    intro n _
    have : t ^ m = WittVector.teichmuller p (ϖ ^ m) := by simp [t, map_pow]
    rw [this]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [WittVector.teichmuller_coeff_zero]; exact Ideal.subset_span rfl
    · rw [WittVector.teichmuller_coeff_pos _ _ n h]; exact J.zero_mem
  have hp' : (u * (p : WittVector p R)) ^ N ∈ I := by
    rw [hmem]
    intro n hn
    rw [mul_pow, WittVector.mul_pow_charP_coeff_zero _ hn]
    exact J.zero_mem
  refine ⟨m + N, fun z n hn => ?_⟩
  have hk : x ^ (m + N) ∈ I := by
    rw [hx]; exact Ideal.add_pow_mem_of_pow_mem_of_le I ht hp' (by omega)
  exact (hmem _).1 (I.mul_mem_right z hk) n hn

end GlobalTheory.WittHighPow
