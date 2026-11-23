import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedSectionsSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountTop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section VeryAmpleEmbedSectionsProof

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}

theorem vaes_ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) :=
  Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact (ratio (S := k) hj l).2)

theorem vaes_mem_pow_of_forall (Q : LineBundle k y) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Q.toSubSystem h) (I : Chart y) {m : ℕ} {s : Ω}
    (hs : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ (Q.toSubSystem.pow (m + e)).sub I) :
    s ∈ (Q.toSubSystem.pow m).sub I := by
  have hs' : ∀ j, h j ≠ 0 → ∃ e : ℕ, s * h j ^ e ∈ Q.toSubSystem.sub I ^ (m + e) := fun j hj => by
    obtain ⟨e, he⟩ := hs j hj
    exact ⟨e, by rw [← SubSystem.pow_sub_eq_pow Q.toSubSystem]; exact he⟩
  rw [SubSystem.pow_sub_eq_pow Q.toSubSystem]
  clear hs
  obtain ⟨P', hPP'⟩ := Q.invertible I
  set P := Q.toSubSystem.sub I with hP
  let c : Ideal (chartRing k y I) := (P ^ m).comap (LinearMap.toSpanSingleton _ Ω s)
  have hc : ∀ a, a ∈ c ↔ (a : Ω) * s ∈ P ^ m := fun a => by
    change a • s ∈ P ^ m ↔ _; rw [chartRing_smul_def]
  have key : ∀ j, ∀ q ∈ P', ∀ a : chartRing k y I, (a : Ω) = h j * q → a ∈ c.radical := by
    intro j q hq a ha
    by_cases hj : h j = 0
    · have : a = 0 := Subtype.ext (by rw [ha, hj, zero_mul]; rfl)
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨e, he⟩ := hs' j hj
    refine ⟨e, (hc _).mpr ?_⟩
    have hmem := Submodule.mul_mem_mul he (Submodule.pow_mem_pow P' hq e)
    rw [pow_add, mul_assoc, ← mul_pow, hPP', one_pow, mul_one] at hmem
    rw [Subalgebra.coe_pow, ha]
    convert hmem using 1
    ring
  let M : Submodule (chartRing k y I) Ω := Submodule.map (Algebra.linearMap (chartRing k y I) Ω) c.radical
  have hle : P * P' ≤ M := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    rw [hP, ← hv.generates I] at hp
    induction hp using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      have h1 : h j * q ∈ P * P' := Submodule.mul_mem_mul
        (by rw [hP, ← hv.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hq
      rw [hPP'] at h1
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      exact ⟨a, key j q hq a ha, ha⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hu
  have h1 : (1 : Ω) ∈ M := hle (by rw [hPP']; exact Submodule.one_le.mp le_rfl)
  obtain ⟨a, ha, ha1⟩ := h1
  have : a = 1 := Subtype.ext ha1
  have ha' : (1 : chartRing k y I) ∈ c.radical := this ▸ ha
  rw [← Ideal.eq_top_iff_one, Ideal.radical_eq_top, Ideal.eq_top_iff_one, hc] at ha'
  simpa using ha'

end VeryAmpleEmbedSectionsProof

theorem VeryAmpleEmbed.Sections.proof : VeryAmpleEmbed.Sections.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h _ hv m
  apply le_antisymm
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun J => ?_
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
    have hsI : ∀ I, s ∈ (Q.toSubSystem.pow m).sub I := fun I =>
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)
    have hb : s / h j ^ m ∈ ampleRing Q.toSubSystem 1 (h j) := Set.mem_iInter.mpr fun I =>
      ⟨m, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hj)]; exact hsI I⟩
    have hbc := vaes_ampleBase_le_chartRing hj (hv.closed j hj hb)
    have hmem : s ∈ twistMod k h (m : ℤ) (singleChart hj) := by
      rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
      exact ⟨⟨_, hbc⟩, by rw [chartRing_smul_def, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hj)]⟩
    exact (Submodule.restrictScalars_mem k _ _).mpr ((twistSys k h (m : ℤ)).mono (singleChart hj) J
      (Finset.singleton_subset_iff.mpr hjJ) s hmem)
  · intro s hs
    refine (Submodule.mem_iInf _).mpr fun I => (Submodule.restrictScalars_mem k _ _).mpr ?_
    refine vaes_mem_pow_of_forall Q hv I fun j hj => ?_
    have hsj : s ∈ twistMod k h (m : ℤ) (singleChart hj) :=
      (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs _)
    obtain ⟨g, t, e, ht, hte, hg, hgt⟩ := exists_rep_of_mem_twistMod h m hj hsj
    have ht' : t ∈ Submonoid.closure {(X j : MvPolynomial (Fin (r + 1)) k)} := by
      have : ((fun i => (X i : MvPolynomial (Fin (r + 1)) k)) ''
          ((({j} : Finset (Fin (r + 1))) : Set (Fin (r + 1))))) = {X j} := by simp
      rw [← this]; exact ht
    obtain ⟨d, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
    have hde : e = d := hte.inj_right (isHomogeneous_X_pow j d) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hde
    refine ⟨e, ?_⟩
    have := aeval_mem_pow Q.toSubSystem hv.mem_secs I hg
    rwa [hgt, map_pow, aeval_X, add_comm] at this

end

end GroundTheory.Heights₂.Heights.Kleiman
