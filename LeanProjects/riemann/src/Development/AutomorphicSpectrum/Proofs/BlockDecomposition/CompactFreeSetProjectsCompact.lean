import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF.Tails

theorem linearIndependent_tails {K : Type} [CommRing K] {M n : ℕ} {Y : Fin (n + 1) → Fin (M + 1) → K}
    (hY : LinearIndependent K Y) (h0 : ∀ i : Fin M, Y 0 i.succ = 0) :
    LinearIndependent K (fun (j : Fin n) (i : Fin M) => Y j.succ i.succ) := by
  have hfree := Fintype.linearIndependent_iff.1 hY

  have hnzd : ∀ b : K, b * Y 0 0 = 0 → b = 0 := by
    intro b hb
    have hsum : ∑ i, (Pi.single 0 b : Fin (n + 1) → K) i • Y i = 0 := by
      rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 1)) (Finset.mem_univ _)
        (fun i _ hi => by simp [Pi.single_eq_of_ne hi])]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb
      · simp [h0 i]
    simpa using hfree _ hsum 0
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have hw' : ∀ i : Fin M, ∑ j, w j * Y j.succ i.succ = 0 := by
    intro i
    have := congrFun hw i
    simpa [Finset.sum_apply] using this
  set r : K := ∑ j, w j * Y j.succ 0 with hr
  have hsum : ∑ i, (Fin.cons (-r) (fun j => Y 0 0 * w j) : Fin (n + 1) → K) i • Y i = 0 := by
    rw [Fin.sum_univ_succ]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply]
      have h1 : ∑ j, Y 0 0 * w j * Y j.succ 0 = r * Y 0 0 := by
        rw [hr, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      ring
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply, h0 i, mul_zero, zero_add]
      have : ∑ j, Y 0 0 * w j * Y j.succ i.succ = Y 0 0 * ∑ j, w j * Y j.succ i.succ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hw' i, mul_zero]
  have hj := hfree _ hsum j.succ
  rw [Fin.cons_succ] at hj
  exact hnzd _ (by rw [mul_comm]; exact hj)

theorem exists_compact_tails (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ)
    (Q : Set (Fin (n + 1) → Fin (M + 1) → K)) (hQ : IsCompact Q)
    (hfree : ∀ Y ∈ Q, LinearIndependent K Y) :
    ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧
      ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  let tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K := fun Y j i => Y j.succ i.succ
  have htl : Continuous tl :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply i.succ).comp (continuous_apply j.succ)
  have hclosed : IsClosed {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} := by
    have : {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} =
        ⋂ i : Fin M, {Y | Y 0 i.succ = 0} := by
      ext Y
      simp
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i.succ).comp (continuous_apply 0)) continuous_const
  refine ⟨tl '' (Q ∩ {Y | ∀ i : Fin M, Y 0 i.succ = 0}), (hQ.inter_right hclosed).image htl, ?_, ?_⟩
  · rintro _ ⟨Y, ⟨hYQ, h0⟩, rfl⟩
    exact linearIndependent_tails (hfree Y hYQ) h0
  · intro A c X h
    exact ⟨vec A c X, ⟨h, fun i => by simp [vec]⟩, by funext j i; simp [tl, vec]⟩

end GlobalTheory.CompanionTheory.SW.StageF.Tails
