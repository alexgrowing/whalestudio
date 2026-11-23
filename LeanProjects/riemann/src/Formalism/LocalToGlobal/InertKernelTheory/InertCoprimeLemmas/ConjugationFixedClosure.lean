import Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

namespace FrFix

variable {p : ℕ} [Fact p.Prime]

theorem not_sq (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) : ¬ ∃ a : ZMod p, a ^ 2 = -(d : ZMod p) := by
  have hleg : legendreSym p (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hleg
  rintro ⟨a, ha⟩
  apply hns
  refine ⟨a, ?_⟩
  push_cast
  rw [← ha]
  ring

theorem fixed_mem_closure (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (z : MaximalUnramifiedExtension p)
    (hz : σ z = z) : (z : ℂ_[p]) ∈ closure (Set.range fun q : ℚ => (q : ℂ_[p])) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ hp1
  have hpk : ‖((p : MaximalUnramifiedExtension p) ^ k)‖ = ((p : ℝ) ^ k)⁻¹ := by rw [norm_pow, hσ.2.2.1, inv_pow]
  have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, w = (p : MaximalUnramifiedExtension p) ^ k * z := ⟨_, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, hpk, inv_mul_le_iff₀ hpkpos, mul_one]
    exact hk.le
  have hσw : σ w = w := by rw [hw, map_mul, map_pow, map_natCast, hz]
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε' : 0 < ε * ((p : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε' (inv_lt_one_of_one_lt₀ hp1)
  obtain ⟨n, hn⟩ := Formalism.L2.Th1.D.fixedIsLimit (MaximalUnramifiedExtension p) p σ hσ w hw1 hσw j
  refine ⟨((n : ℚ) / (p : ℚ) ^ k : ℚ), ⟨_, rfl⟩, ?_⟩
  have hpk0 : ((p : MaximalUnramifiedExtension p) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hq : ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : ℂ_[p]) = ((((n : ℚ) / (p : ℚ) ^ k : ℚ) : MaximalUnramifiedExtension p) : ℂ_[p]) :=
    (map_ratCast (MaximalUnramifiedExtension p).subtype _).symm
  have e : z - ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : MaximalUnramifiedExtension p) = ((p : MaximalUnramifiedExtension p) ^ k)⁻¹ * (w - n) := by
    rw [hw]
    push_cast
    field_simp
  rw [hq, ← Subtype.dist_eq, dist_eq_norm, e, norm_mul, norm_inv, hpk, inv_inv]
  calc (p : ℝ) ^ k * ‖w - n‖ ≤ (p : ℝ) ^ k * ((p : ℝ) ^ j)⁻¹ := by gcongr
    _ = (p : ℝ) ^ k * ((p : ℝ)⁻¹) ^ j := by rw [inv_pow]
    _ < (p : ℝ) ^ k * (ε * ((p : ℝ) ^ k)⁻¹) := by gcongr
    _ = ε := by field_simp

end FrFix

theorem conjugation_fixed_closure : FixConj := by
  intro D p _ h5 hj lam ι hι σ hσ y hy
  have hsq : Squarefree D.host.d := (Nat.prime_iff.mp D.host.hyp.2.1).squarefree
  have h4 : D.host.d % 4 = 3 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D
  obtain ⟨hwm, hws⟩ := Formalism.L2.Th1.D.sqrt_in_unramified_completion D.host.d hsq h4 p h5 (FrFix.not_sq D.host.d hj) ι
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, (w : ℂ_[p]) = ι (omegaK D.host.d) := ⟨⟨_, hwm⟩, rfl⟩
  have hσw : σ w = 1 - w := hws σ hσ w hw
  have hLI := Formalism.L2.KerInert.lamCIota p lam ι hι
  have hlc : ∀ z : D.host.E, lamC lam (D.host.φ₀ z) = ι (D.host.φ₀ z) :=
    fun z => hLI.1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D z)
  have hsK : D.host.sqrtMinusD ∈ D.host.K := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D
  have hx2 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrtE_sq D, map_neg, map_natCast]
  have hom : (2 * omegaK D.host.d - 1) ^ 2 = -(D.host.d : ℂ) := by
    unfold omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq

  have c2 : ((2 : MaximalUnramifiedExtension p) : ℂ_[p]) = 2 := map_ofNat (MaximalUnramifiedExtension p).subtype 2
  obtain ⟨rK, hrK, hσr⟩ : ∃ rK : MaximalUnramifiedExtension p, (rK : ℂ_[p]) = ι (D.host.φ₀ D.host.sqrtMinusD) ∧ σ rK = -rK := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · refine ⟨2 * w - 1, ?_, ?_⟩
      · rw [h, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
    · refine ⟨1 - 2 * w, ?_, ?_⟩
      · rw [h, map_neg, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]; ring
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
  have hd0 : (D.host.d : ℂ_[p]) ≠ 0 := by exact_mod_cast (D.host.hyp.2.1).ne_zero
  have hr0 : rK ≠ 0 := by
    intro h
    have h' : ((rK : ℂ_[p])) ^ 2 = 0 := by rw [h]; simp
    rw [hrK, ← map_pow, hx2, map_neg, map_natCast, neg_eq_zero] at h'
    exact hd0 h'

  have h2 : (2 : MaximalUnramifiedExtension p) ≠ 0 := two_ne_zero
  obtain ⟨u, hu⟩ : ∃ u : MaximalUnramifiedExtension p, u = (y + σ y) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : MaximalUnramifiedExtension p, v = (y - σ y) / (2 * rK) := ⟨_, rfl⟩
  have hσu : σ u = u := by rw [hu, map_div₀, map_add, hy, map_ofNat]; ring
  have hσv : σ v = v := by
    rw [hv, map_div₀, map_sub, map_mul, hy, hσr, map_ofNat]
    field_simp
    ring
  have hyuv : y = u + v * rK := by
    rw [hu, hv]
    field_simp
    ring
  have cu := FrFix.fixed_mem_closure σ hσ u hσu
  have cv := FrFix.fixed_mem_closure σ hσ v hσv
  have hyc : (y : ℂ_[p]) = (u : ℂ_[p]) + (v : ℂ_[p]) * (rK : ℂ_[p]) := by rw [hyuv]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · have hcont : Continuous fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]) := by fun_prop
    have hmem : ((u : ℂ_[p]), (v : ℂ_[p])) ∈ closure ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ
        (Set.range fun q : ℚ => (q : ℂ_[p]))) := by
      rw [closure_prod_eq]; exact ⟨cu, cv⟩
    have hmaps : Set.MapsTo (fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]))
        ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ (Set.range fun q : ℚ => (q : ℂ_[p])))
        (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) := by
      rintro ⟨_, _⟩ ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine ⟨(a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩, ?_⟩
      have e : (((a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩ : D.host.K) : D.host.E) =
          (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
        push_cast; rfl
      simp only
      rw [e, hlc, hrK, map_add, map_mul, map_ratCast, map_ratCast, map_add, map_mul, map_ratCast, map_ratCast]
    have hh := map_mem_closure hcont hmem hmaps
    rw [hyc]
    exact hh
  · intro σp hσp
    have hσc : Continuous σp :=
      AddMonoidHomClass.continuous_of_bound σp 1 (fun z => by rw [hσp.2 z, one_mul])
    have hfixS : closure (Set.range fun q : ℚ => (q : ℂ_[p])) ⊆ {z | σp z = z} :=
      closure_minimal (by rintro _ ⟨q, rfl⟩; exact map_ratCast σp q) (isClosed_eq hσc continuous_id)
    have hu' : σp u = u := hfixS cu
    have hv' : σp v = v := hfixS cv
    have hr' : σp (rK : ℂ_[p]) = -(rK : ℂ_[p]) := by
      have h := hσp.1 ⟨D.host.sqrtMinusD, hsK⟩
      have hc : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.BasicNotions.Examples₂.conj_bE D.host
      change σp (lamC lam (D.host.φ₀ D.host.sqrtMinusD)) =
        lamC lam (D.host.φ₀ (D.host.conj D.host.sqrtMinusD)) at h
      rw [hc, hlc, hlc, map_neg, map_neg, ← hrK] at h
      exact h
    rw [hyc, map_add, map_mul, hu', hv', hr', hyuv, map_add, map_mul, hσu, hσv, hσr]
    push_cast
    ring

end Formalism.L2.KerInert
