import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

theorem torsion_integral : TorsionIntegral := by
  intro K _ _ inst W hW P N hN hNP hP
  obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hW
  have e : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst e
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact Formalism.ELL.torsionIntegral.{0} K W ⟨h1, h2, h3, h4, h6⟩ hΔ N hN x y h hNP

open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)

namespace Tor

section Lat

variable (L : PeriodPair)

theorem int_mul_mem (k : ℤ) {x : ℂ} (hx : x ∈ L.lattice) : (k : ℂ) * x ∈ L.lattice := by
  simpa using L.lattice.smul_mem k hx

theorem nat_mul_mem (k : ℕ) {x : ℂ} (hx : x ∈ L.lattice) : (k : ℂ) * x ∈ L.lattice := by
  simpa using int_mul_mem L (k : ℤ) hx

end Lat

theorem omegaK_sq (d : ℕ) :
    Formalism.L2.Th1.CM.omegaK d ^ 2 = Formalism.L2.Th1.CM.omegaK d - ((d : ℂ) + 1) / 4 := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hI := Complex.I_sq
  unfold Formalism.L2.Th1.CM.omegaK
  linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4) * h

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem norm_natCast {N : ℕ} (h : ¬ l ∣ N) : ‖(N : ℂ_[l])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' l (N : ℚ_[l])
  rw [Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)] at h1
  simpa using h1

open Classical in
theorem nsmul_ptOf (hA : PtOfAdd) (hZ : PtOfZero) (t : ℂ) (N : ℕ) :
    N • ptOf l L ι t = ptOf l L ι ((N : ℂ) * t) := by
  induction N with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    exact ((hZ l L ι 0).2 (zero_mem _)).symm
  | succ n ih =>
    rw [succ_nsmul, ih, ← hA]
    congr 1
    push_cast
    ring

open Classical in

def piOf (hA : PtOfAdd) : ℂ →+ (curveL l L ι).toAffine.Point :=
  AddMonoidHom.mk' (ptOf l L ι) (hA l L ι)

open Classical in

theorem restrict (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hW : IntCurve (curveL l L ι)) (t : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N)
    (hNt : (N : ℂ) * t ∈ L.lattice) :
    IntPts (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype) ∧
    IsTransSys (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype)
      (fun s : AddSubgroup.zmultiples t => gT l L ι (s : ℂ)) := by
  constructor
  · rintro ⟨s, hs⟩ h0
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hs
    refine hI l L ι hW _ N hN hlN ?_ (fun hmem => h0 ((hZ l L ι _).2 hmem))
    have e : (N : ℂ) * (k • t) = (k : ℂ) * ((N : ℂ) * t) := by
      rw [zsmul_eq_mul]
      ring
    change (N : ℂ) * (k • t) ∈ L.lattice
    rw [e]
    exact int_mul_mem L k hNt
  · obtain ⟨h1, h2, h3⟩ := hS l L ι (piOf l L ι hA) (fun _ => rfl)
    exact ⟨fun s => h1 s, fun s => h2 s, fun P Q => h3 P Q⟩

theorem cc_log : constantCoeff (Formalism.L2.Th1.A.logSer (curveL l L ι)) = 0 :=
  (Formalism.L2.Th1.A.logSpec.{0} ℂ_[l] (curveL l L ι)).1

theorem cc_phL : constantCoeff (phL l L ι) = 0 :=
  Formalism.L2.Th1.B.Ph.constantCoeff_phO _ _ (cc_log l L ι)
    (Formalism.L2.Th1.A.logSpec.{0} ℂ_[l] (curveL l L ι)).2.1

theorem cc_fExp_phL : constantCoeff (fExp (phL l L ι)) = 1 :=
  Formalism.L2.Th1.B.constantCoeff_fExp (cc_phL l L ι)

theorem cc_inU (f : ℂ → ℂ) : constantCoeff (inU l L ι f) = ι (f 0) := by
  rw [inU, Formalism.L2.Th1.B.Ph.constantCoeff_psubst (cc_log l L ι), ← coeff_zero_eq_constantCoeff_apply,
    coeff_map, taylor0, coeff_mk]
  simp

theorem cc_gT (t : ℂ) : constantCoeff (gT l L ι t) = ι (opU L t (sgStar L) 0) := by
  rw [gT, map_mul, cc_fExp_phL, one_mul, cc_inU]

theorem taylor0_const_mul (a : ℂ) (f : ℂ → ℂ) : taylor0 (fun z => a * f z) = C a * taylor0 f := by
  ext n
  simp [taylor0, mul_div_assoc]

theorem inU_const_mul (a : ℂ) (f : ℂ → ℂ) :
    inU l L ι (fun z => a * f z) = C (ι a) * inU l L ι f := by
  rw [inU, taylor0_const_mul, map_mul, map_C, Formalism.L2.Th1.B.Ph.psubst_C_mul (cc_log l L ι)]
  rfl

end An

theorem gaussOne_C_mul {K : Type} [NormedField K] {a : K} {f : K⟦X⟧} (ha : ‖a‖ = 1)
    (hf : GaussOne f) : GaussOne (C a * f) := by
  obtain ⟨h1, n, hn⟩ := hf
  refine ⟨fun m => ?_, n, ?_⟩
  · rw [coeff_C_mul, norm_mul, ha, one_mul]
    exact h1 m
  · rw [coeff_C_mul, norm_mul, ha, one_mul, hn]

end Tor

open Tor

open Classical in

theorem PtOfInt_of (hA : PtOfAdd) (hZ : PtOfZero) (hT : TorsionIntegral) : PtOfInt := by
  intro l _ L ι hW t N _ hlN hNt ht
  refine hT ℂ_[l] (curveL l L ι) hW (ptOf l L ι t) N (norm_natCast l hlN) ?_ ?_
  · rw [nsmul_ptOf l L ι hA hZ]
    exact (hZ l L ι _).2 hNt
  · exact fun h => ht ((hZ l L ι t).1 h)

theorem KernelPtInt_of (hI : PtOfInt) : KernelPtInt := by
  intro d L hd hCM l _ ι hW a b t hαt hl ht
  have hn0 : a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) ≠ 0 := fun h => hl (h ▸ dvd_zero _)
  have hq : ((((d : ℤ) + 1) / 4 : ℤ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have h4 : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
    rw [h4]
    ring
  have hnt : ((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) : ℤ) : ℂ) * t ∈ L.lattice := by
    have e : ((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) : ℤ) : ℂ) * t =
        ((a + b : ℤ) : ℂ) * (((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t) -
          (b : ℂ) * (Formalism.L2.Th1.CM.omegaK d * (((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t)) := by
      push_cast
      rw [hq]
      linear_combination ((b : ℂ) ^ 2 * t) * omegaK_sq d
    rw [e]
    exact sub_mem (int_mul_mem L _ hαt) (int_mul_mem L _ (hCM _ hαt))
  refine hI l L ι hW t (a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs
    (Int.natAbs_pos.2 hn0) (fun h => hl (Int.natCast_dvd.2 h)) ?_ ht
  have e2 : (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℕ) : ℂ) =
      (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℤ) : ℂ) := by
    simp
  rw [e2]
  rcases Int.natAbs_eq (a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)) with h | h
  · rw [← h]
    exact hnt
  · have h' : (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℤ)) =
        -(a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)) := by omega
    rw [h', Int.cast_neg, neg_mul]
    exact neg_mem hnt

open Classical in

theorem AnalyticTrans_of (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hU : TransUnit) : AnalyticTrans := by
  intro l _ L ι hW t N hN hlN hNt ht
  obtain ⟨hIP, hTS⟩ := restrict l L ι hS hA hZ hI hW t N hN hlN hNt
  have h := hU ℂ_[l] (curveL l L ι) hW (AddSubgroup.zmultiples t) _ _ hIP hTS
    ⟨t, AddSubgroup.mem_zmultiples t⟩ N (norm_natCast l hlN)
    (by
      change N • ptOf l L ι t = 0
      rw [nsmul_ptOf l L ι hA hZ]
      exact (hZ l L ι _).2 hNt)
    (fun h0 => ht ((hZ l L ι t).1 h0))
  simpa only [cc_gT] using h

open Classical in

theorem Th0Analytic_of (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hU : TransUnit) (hG : TransGauss) (hO : OpUTh0Root) : ThetaZeroAnalytic := by
  intro l _ L ι hl2 hW ω₀ hω hω2
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ := by
      push_cast
      ring
    rw [e]
    exact hω
  obtain ⟨hc1, hOne⟩ := AnalyticTrans_of hS hA hZ hI hU l L ι hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hιc : ι (opU L (ω₀ / 2) (sgStar L) 0) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc1
    exact zero_ne_one hc1
  have hc : opU L (ω₀ / 2) (sgStar L) 0 ≠ 0 := fun h0 => hιc (by rw [h0, map_zero])
  have hth : th0 L (ω₀ / 2) =
      fun z => (opU L (ω₀ / 2) (sgStar L) 0)⁻¹ * opU L (ω₀ / 2) (sgStar L) z := by
    funext z
    rw [th0, div_eq_inv_mul]
  have hin : inU l L ι (th0 L (ω₀ / 2)) =
      C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * inU l L ι (opU L (ω₀ / 2) (sgStar L)) := by
    rw [hth, inU_const_mul, map_inv₀]
  have hcc : constantCoeff (inU l L ι (th0 L (ω₀ / 2))) = 1 := by
    rw [cc_inU, th0, div_self hc, map_one]
  have key : fExp (phL l L ι - phPrime l L ι (ω₀ / 2)) =
      C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * gT l L ι (ω₀ / 2) := by
    rw [phPrime, sub_neg_eq_add,
      Formalism.L2.Th1.B.fExp_add (cc_phL l L ι) (Formalism.L2.Th1.B.constantCoeff_fLog hcc),
      Formalism.L2.Th1.B.fExp_fLog hcc, hin, gT]
    ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change constantCoeff (phL l L ι - phPrime l L ι (ω₀ / 2)) = 0
    have h1 : constantCoeff (fLog (inU l L ι (th0 L (ω₀ / 2)))) = 0 :=
      Formalism.L2.Th1.B.constantCoeff_fLog hcc
    rw [phPrime, sub_neg_eq_add, map_add, cc_phL, h1, add_zero]
  · change Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) (fExp (phL l L ι - phPrime l L ι (ω₀ / 2)))
    rw [key]
    exact (Ser.intS_iff_integral _).1 hOne.2
  · intro t N hN hlN hNt
    have hN2 : ¬ l ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
    have e1 : ((2 * N : ℕ) : ℂ) * t = ((2 : ℕ) : ℂ) * ((N : ℂ) * t) := by
      push_cast
      ring
    have e2 : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) = (N : ℂ) * ω₀ := by
      push_cast
      ring
    have m1 : ((2 * N : ℕ) : ℂ) * t ∈ L.lattice := by
      rw [e1]
      exact nat_mul_mem L 2 hNt
    have m2 : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
      rw [e2]
      exact nat_mul_mem L N hω
    have m3 : ((2 * N : ℕ) : ℂ) * (t + ω₀ / 2) ∈ L.lattice := by
      rw [mul_add]
      exact add_mem m1 m2
    obtain ⟨ζ, m, hm, hζ, hop⟩ := hO L t (ω₀ / 2) (2 * N) (by omega) m1 m2 hω2
    have hζ1 : ‖ι ζ‖ = 1 := by
      have h1 : ‖ι ζ‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, hζ, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
    obtain ⟨hIP, hTS⟩ := restrict l L ι hS hA hZ hI hW (t + ω₀ / 2) (2 * N) (by omega) hN2 m3
    have hg : GaussOne (gT l L ι (t + ω₀ / 2)) :=
      hG ℂ_[l] (curveL l L ι) hW (AddSubgroup.zmultiples (t + ω₀ / 2)) _ _ hIP hTS
        ⟨t + ω₀ / 2, AddSubgroup.mem_zmultiples _⟩ (2 * N) (norm_natCast l hN2)
        (by
          change (2 * N) • ptOf l L ι (t + ω₀ / 2) = 0
          rw [nsmul_ptOf l L ι hA hZ]
          exact (hZ l L ι _).2 m3)
    have e3 : fExp (phL l L ι) * inU l L ι (opU L t (th0 L (ω₀ / 2))) =
        C (ι (ζ * (opU L (ω₀ / 2) (sgStar L) 0)⁻¹)) * gT l L ι (t + ω₀ / 2) := by
      rw [hop, inU_const_mul, gT]
      ring
    rw [e3]
    refine gaussOne_C_mul ?_ hg
    rw [map_mul, map_inv₀, norm_mul, norm_inv, hζ1, hc1, inv_one, one_mul]

end Formalism.L2.Th1.E
