import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowSq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq D.host.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem diff_avoid (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ t ∈ differentIdeal ℤ (𝓞 D.host.F), algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∉ P.asIdeal := by
  have hPp := P.isPrime
  let v : HeightOneSpectrum (𝓞 D.host.F) :=
    ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.IsPrime.comap _, by
      intro hb
      apply P.ne_bot
      have hg0 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap, map_natCast]; exact hP
      rw [hb, Ideal.mem_bot] at hg0
      exfalso
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact this (by exact_mod_cast hg0)⟩
  have hgi : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have hg : ((gS D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      show _ ∈ P.asIdeal.comap _
      rw [Ideal.mem_comap, map_natCast]; exact hP
    unfold Lat.gS at hg
    rw [Nat.cast_mul] at hg
    rcases v.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hgi
  have hnd := not_dvd_diff v i hi
  by_contra hc
  push Not at hc
  exact hnd (Ideal.dvd_iff_le.2 fun t ht => hc t ht)

end Formalism.L2.SG.Pf.FibD
