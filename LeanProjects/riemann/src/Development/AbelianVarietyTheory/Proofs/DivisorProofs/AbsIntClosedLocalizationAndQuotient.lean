import Mathlib
open IsLocalRing

namespace GlobalTheory

open Polynomial

theorem absIntClosed_localization_and_quotient : ∀ (T : Type) [CommRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∀ (M : Submonoid T), 0 ∉ M → (IsDomain (Localization M) ∧ ∀ f : Polynomial (Localization M), f.Monic → 0 < f.natDegree → ∃ x : (Localization M), f.eval x = 0)) ∧ (∀ (p : Ideal T), p.IsPrime → (IsDomain (T ⧸ p) ∧ ∀ f : Polynomial (T ⧸ p), f.Monic → 0 < f.natDegree → ∃ x : (T ⧸ p), f.eval x = 0)) := by
  intro T _ ⟨hdom, hroot⟩
  refine ⟨fun M hM => ?_, fun p hp => ?_⟩
  · have hle : M ≤ nonZeroDivisors T := le_nonZeroDivisors_of_noZeroDivisors hM
    haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M f
      (by rw [hf.leadingCoeff]; exact one_mem _)
    obtain ⟨g, hg, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hf)
    rw [natDegree_scaleRoots] at hgdeg
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    set s : Localization M :=
      algebraMap T (Localization M) (IsLocalization.commonDenom M f.support f.coeff) with hs
    have hu : IsUnit s := IsLocalization.map_units _ _
    refine ⟨algebraMap T (Localization M) y * ↑hu.unit⁻¹, ?_⟩
    have key := scaleRoots_eval_mul f (algebraMap T (Localization M) y * ↑hu.unit⁻¹) s
    have hsr : s * (algebraMap T (Localization M) y * ↑hu.unit⁻¹) =
        algebraMap T (Localization M) y := by
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    rw [hsr, ← hg, eval_map, eval₂_hom, hy, map_zero] at key
    exact ((hu.pow _).mul_right_eq_zero).1 key.symm
  · haveI := hp
    haveI : IsDomain (T ⧸ p) := Ideal.Quotient.isDomain p
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl : f ∈ lifts (Ideal.Quotient.mk p) :=
      (mem_lifts _).2 (map_surjective _ Ideal.Quotient.mk_surjective f)
    obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic hl hf
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    refine ⟨Ideal.Quotient.mk p y, ?_⟩
    rw [← hg, eval_map, eval₂_hom, hy, map_zero]

end GlobalTheory
