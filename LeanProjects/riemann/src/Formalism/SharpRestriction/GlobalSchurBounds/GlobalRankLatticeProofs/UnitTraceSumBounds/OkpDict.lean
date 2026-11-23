import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

noncomputable def conjK : D.host.K →+* D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)

theorem conjK_coe (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x

noncomputable def tauKp : D.host.K →+* ℂ_[p] :=
  lam.comp ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun _ => test_vector_mem_schwartz_bruhat D _))

theorem tauKp_apply (x : D.host.K) : tauKp D lam x = lamC lam (D.host.φ₀ (x : D.host.E)) := by
  unfold tauKp lamC
  first
  | rfl
  | (simp [test_vector_mem_schwartz_bruhat]; done)
  | (rw [dif_pos (test_vector_mem_schwartz_bruhat D _)]; rfl)

theorem conjK_ne : ∃ x, conjK D x ≠ x := by
  have hd : 0 < D.host.d := by
    have := D.host.qd_big.2
    omega
  refine ⟨⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd⟩, ?_⟩
  intro h
  have h1 := congrArg (fun y : D.host.K => (y : D.host.E)) h
  simp only at h1
  rw [conjK_coe] at h1
  change D.host.conj D.host.sqd = D.host.sqd at h1
  rw [Formalism.HC.HostRaw.conj_sqd] at h1
  have h2 : (2 : D.host.E) * D.host.sqd = 0 := by linear_combination -h1
  have hs : D.host.sqd = 0 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h3 := D.host.sqd_sq
  rw [hs] at h3
  have h4 : (D.host.d : D.host.E) = 0 := by linear_combination h3
  have h5 : D.host.d = 0 := by exact_mod_cast h4
  omega

theorem okp_eq : OKp D lam = closure (Set.range fun a : 𝓞 D.host.K => (tauKp D lam (a : D.host.K), tauKp D lam (conjK D (a : D.host.K)))) := by
  unfold OKp
  congr 2
  funext a
  simp only [tauKp_apply, conjK_coe]
  first
  | rfl
  | (unfold tauK tauKc; rfl)
  | (simp only [tauK, tauKc]; done)
  | (simp [tauK, tauKc]; done)

theorem exists_sqrt_K : ∃ b : D.host.K, b ^ 2 = -(D.host.d : D.host.K) := by
  refine ⟨⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd⟩, ?_⟩
  apply (algebraMap D.host.K D.host.E).injective
  rw [map_pow, map_neg, map_natCast]
  exact D.host.sqd_sq

end Formalism.MainNotions.Ext
