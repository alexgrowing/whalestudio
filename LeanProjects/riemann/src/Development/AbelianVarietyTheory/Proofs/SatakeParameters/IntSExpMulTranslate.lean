import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD

noncomputable section

open scoped BigOperators
open Formalism.L2.Th1
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace GlobalTheory.ThLoc

theorem endoDatum_of_model (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (hCM : HasCMBy d L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W)
    (hW : IntCurve W) (m n : ℤ) (hN : ¬ (p : ℤ) ∣ normInt d m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK d)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d)) =
        (Fintype.card S : ℂ_[p]) + 1 ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) *
          (ι ((m : ℂ) + (n : ℂ) * omegaK d) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d))) *
          ι (F.s2 L) = ∑ P, (xP P + W.b₂ / 12) := by
  have hN0 : normInt d m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ := D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hpt : ∀ P : S, E.ptW p L ι W (P : ℂ) =
      .some _ _ (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2) := by
    intro P
    unfold E.ptW
    rw [dif_pos ⟨(hker P).2, E.AnaSysW.nonsing hU (P : ℂ) (hker P).2⟩]
  have hint : ∀ P : S, ‖E.AnaSysW.xc p L ι W P‖ ≤ 1 ∧ ‖E.AnaSysW.yc p L ι W P‖ ≤ 1 := by
    intro P
    have h := E.TransW.ptW_int E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW (P : ℂ) (S.card + 1) hpN
      (hker P).1 (hker P).2
    rw [hpt P] at h
    exact h
  refine ⟨S, neg, fun P => E.AnaSysW.xc p L ι W P, fun P => E.AnaSysW.yc p L ι W P,
    ?_, fun P => (hint P).1, fun P => (hint P).2, ?_, ?_⟩
  · apply D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2).1
    · intro P
      constructor
      · simp only [E.AnaSysW.xc, (hnegP P).1]
      · simp only [WeierstrassCurve.Affine.negY, E.AnaSysW.xc, E.AnaSysW.yc]
        rw [(hnegP P).2, (hnegP P).1, map_neg]
        ring
    · have h := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, E.AnaSysW.xc, sub_add_cancel]
      rw [E.weierstrass_series_eq_transported p L ι W hU]
      exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp
  · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum]
    simp [E.AnaSysW.xc]

theorem jets_phW_three (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (h3 : d % 3 = 2) (hCM : HasCMBy d L)
    (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]) (hU : Unif 3 L ι W) (hW : IntCurve W)
    (i : ℕ) (hi : 1 ≤ i) : ‖C.jet (logSer W) (E.phW 3 L ι W) i‖ ≤ 1 := by
  have hnorm : normInt d (-1) 2 = d := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have hdiv : ((d : ℤ) + 1) / 4 = k := by omega
    unfold normInt
    rw [hdiv]
    linear_combination -hk
  have hN : ¬ ((3 : ℕ) : ℤ) ∣ normInt d (-1) 2 := by
    rw [hnorm]
    omega
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ :=
    endoDatum_of_model d L hmod hCM 3 ι W hU hW (-1) 2 hN
  set al := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) with hal
  set albar := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) with halbar
  have hsum : al + albar = ((0 : ℤ) : ℂ_[3]) := by
    rw [hal, halbar, ← map_add]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) +
        (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) = 0 := by
      push_cast
      ring
    rw [e]
    simp
  have hsq : al ^ 2 = -(d : ℂ_[3]) := by
    rw [hal, ← map_pow]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) ^ 2 = -(d : ℂ) := by
      push_cast
      linear_combination 4 * D.CurveNormEndomorphisms.omega_sq d
    rw [e, map_neg, map_natCast]
  have h2 : ‖(2 : ℂ_[3])‖ = 1 := Top.OrthogonalGaussModelNormLemmas.norm_two 3 (by norm_num)
  have hal1 : ‖al‖ = 1 := by
    have h1 := congrArg norm hsq
    rw [norm_pow, norm_neg, E.ScaledModelNorms.norm_nat 3 (show ¬ 3 ∣ d by omega)] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  have hdiff : ‖al - albar‖ = 1 := by
    have e : al - albar = 2 * al := by
      have := hsum
      push_cast at this
      linear_combination -this
    rw [e, norm_mul, h2, hal1, one_mul]
  have hb : ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 3 * k := ⟨(d + 1) / 3, by omega⟩
    have hk' : (d : ℂ_[3]) + 1 = 3 * (k : ℂ_[3]) := by exact_mod_cast hk
    have e : (al ^ 2 - 1) * (W.b₂ / 12) = -((k : ℂ_[3]) * W.b₂) / 2 ^ 2 := by
      rw [hsq]
      linear_combination (-W.b₂ / 12) * hk'
    have hb2 : ‖W.b₂‖ ≤ 1 := by
      have hm : W.b₂ ∈ unitBall ℂ_[3] := by
        obtain ⟨a1, a2, -⟩ := Top.OrthogonalGaussModelNormLemmas.coeffIn hW
        unfold WeierstrassCurve.b₂
        exact add_mem (pow_mem a1 2) (mul_mem (ofNat_mem _ 4) a2)
      exact hm
    rw [e, norm_div, norm_pow, h2, one_pow, div_one, norm_neg, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ k) (norm_nonneg _) hb2
  have h := G.curveJetsUnramThm ℂ_[3] W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW) h2 (ι (F.s2 L)) al albar 0 S neg xP yP
    hE hx hy hprod hal1 hsum hdiff hb hs i hi
  unfold E.phW
  rw [← E.weierstrass_series_eq_transported 3 L ι W hU]
  exact h

theorem intS_exp_mul_translate (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p])
    (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W) (hW : IntCurve W) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice)
    (hω2 : ω₀ / 2 ∉ L.lattice) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ p ∣ N)
    (hNs : (N : ℂ) * s ∈ L.lattice) :
    E.IntS (B.fExp (E.phW p L ι W) * E.inW p ι W (F.opU L s (F.th0 L (ω₀ / 2)))) := by
  have hl2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by simpa using E.TransW.half_mem hω 1
  obtain ⟨hc1, -⟩ := E.analytic_translate_model p L ι W hU hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hN2 : ¬ p ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
  have m3 : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    rw [mul_add]
    exact add_mem (E.TransW.two_mem hNs) (E.TransW.half_mem hω N)
  have hsim := (E.TransW.hW_sim p L ι W (ω₀ / 2) s (2 * N) (by omega) (E.TransW.two_mem hNs)
    (E.TransW.half_mem hω N) hω2).mul_left (B.fExp (E.phW p L ι W))
  refine (hsim.gaussOne ?_).1
  rw [mul_left_comm, ← E.TransW.gW_eq]
  exact E.Tor.gaussOne_C_mul (by rw [norm_inv, hc1, inv_one])
    (E.TransW.gW_gauss E.analytic_translate_system_model E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW _ (2 * N) hN2 m3)

theorem thetaZJetsThree : ThetaZJetsThree := by
  intro d L hd8 hd3 hCM ι W hU hW ω₀ hω h1 _ n _ κ _ r s N hr hN h3N hs
  have hω2 : ω₀ / 2 ∉ L.lattice := fun h => h1 (hCM _ h)
  obtain ⟨hlp, -, -, -, hu⟩ := C.curveFrame ℂ_[3] (unitBall ℂ_[3]) W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW)
  have hph : PowerSeries.constantCoeff (E.phW 3 L ι W) = 0 := E.AnaSysW.cc_phW 3 L ι W
  obtain ⟨e1, hInt⟩ := E.prodInt ℂ_[3] κ n (E.phW 3 L ι W) r
    (fun k i => B.fExp (E.phW 3 L ι W) * E.inW 3 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))))
    hph hr (fun k i => intS_exp_mul_translate 3 (by norm_num) L ι W hU hW ω₀ hω hω2 (s k i) N hN h3N
      (hs k i))
  have key := (G.kernelTwo ℂ_[3] _ _ _ hlp hu hph
    (jets_phW_three d L (by omega) hd3 hCM ι W hU hW) n (fun _ => 1) (fun _ => by simp) _
    (fun m => hInt m)).1
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  rw [Top.KJ.phSum_one] at key
  change Formalism.DworkPowerSeriesWeights.JetsIntegral (G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)) at key
  rw [← e1, Top.KJ.toZ_thetaProd hv0] at key
  convert key using 1
  unfold Top.thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (B.fExp (-(E.phW 3 L ι W)) * _)
  rw [← mul_assoc, ← B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, B.ParO.fExp_zero, one_mul]
  unfold E.inW
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end GlobalTheory.ThLoc
