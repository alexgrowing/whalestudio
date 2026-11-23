import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LengthIndex.MemDualLat

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

lemma idx_le (hI : IdxCalc) (hG : A.Good) {f : Module.End K A.V} (hf : f * f = f) {n : ℕ}
    (hn0 : 0 < n) (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) (w : HeightOneSpectrum (𝓞 K)) :
    idxAt w (imgE A f A.L) (cutE A f A.L) ≤ (dimE A f : ℤ) * vAdd w ((n : ℕ) : K) := by
  have h := (hI K A.V w (imgE A f A.L) (cutE A f A.L) (fg_img A hG f) (fg_cut A hG f)
    (span_cut_eq A hf hn0 hn)).2.2.2.2.2 n hn0 (part2 A hf) (part1 A hn)
  rwa [rk_img A hG f] at h

lemma idx_eq_len (w : HeightOneSpectrum (𝓞 K)) {f : Module.End K A.V} (hf : f * f = f) :
    idxAt w (imgE A f A.L) (cutE A f A.L) = ((lenAt w (imgE A f A.L) (cutE A f A.L)).toNat : ℤ) := by
  unfold idxAt
  rw [lenAt_eq_zero w (part2 A hf)]
  simp

end

theorem projA_of (hI : IdxCalc) : ProjA := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, hn0, he, hn, -⟩ := hP
  have he1 := one_sub_idem A he
  have hn1 := one_sub_int A hn
  refine ⟨part1 A hn, part2 A he, ⟨quotEquiv A e⟩, fun w => ?_,
    fun ψ hψ => dual_part A hG he hn0 hn ψ hψ⟩
  have heq : idxAt w (imgE A e A.L) (cutE A e A.L) =
      idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) := by
    rw [idx_eq_len A w he, idx_eq_len A w he1, lenAt_congr w _ _ _ _ (quotEquiv A e)]
  refine ⟨heq, by rw [idx_eq_len A w he]; positivity, ?_⟩
  rcases le_total (dimE A e) (dimE A (1 - e)) with h | h
  · rw [min_eq_left h]
    exact idx_le A hI hG he hn0 hn w
  · rw [min_eq_right h, heq]
    exact idx_le A hI hG he1 hn0 hn1 w

end PI.Dv.ProjAW

theorem dvProjA_of (hI : PI.Dv.IdxCalc) : PI.Dv.ProjA := PI.Dv.ProjAW.projA_of hI
