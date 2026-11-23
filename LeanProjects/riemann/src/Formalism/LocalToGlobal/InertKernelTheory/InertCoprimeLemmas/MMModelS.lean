import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

noncomputable section

namespace Formalism.L2.KerInert.MModelS

open PowerSeries
open Formalism.L2.Th1.A (shortW logSer expSer wpReg)
open Formalism.L2.KerInert.MModel (scaleVC scaleVC_smul param sig_at X_mul_shift)

variable {p : ℕ} [Fact p.Prime]

theorem uinv_mul_scale (C : WeierstrassCurve.VariableChange ℂ_[p]) (a : ℂ_[p]ˣ) :
    (((C * scaleVC a).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (a : ℂ_[p]) := by
  simp [scaleVC, WeierstrassCurve.VariableChange.mul_def, mul_comm]

section EPart

open Formalism.L2.Th1.B (fExp fExp_add constantCoeff_fExp)

theorem ePartS (h5 : 5 ≤ p) (g2 g3 ε s2 a : ℂ_[p]) (hε0 : ε ≠ 0) (ha0 : a ≠ 0) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p])
    (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (hsg : Formalism.MainNotions.TaylorLogMetric.sgSer lam Λ =
      Formalism.L2.Th1.B.sgStar ((a * ε) ^ 2 * s2) (Formalism.L2.Th1.F.pOf ((a * ε) ^ 4 * g2) ((a * ε) ^ 6 * g3)))
    (hu1 : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * a‖ = 1) (h : PowerSeries ℂ_[p]) (hh0 : constantCoeff h = 0)
    (hhI : ∀ n, ‖coeff n h‖ ≤ 1)
    (hlog : PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) *
      (Formalism.MainNotions.TaylorLogMetric.flog (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq).subst h = PowerSeries.C a⁻¹ * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) :
    ∃ Uu : PowerSeries ℂ_[p], (∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (coeff n Uu)) ∧
      (Formalism.MainNotions.TaylorLogMetric.ePhi1 lam Λ C wq)⁻¹.subst h = Uu * fExp (ι := Unit) (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
  have hp2 : 2 ≤ p := by omega
  set ep : ℂ_[p] := ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hep
  have hep0 : ep ≠ 0 := Units.ne_zero _
  set fl := Formalism.MainNotions.TaylorLogMetric.flog (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq with hfl
  have hfl0 : constantCoeff fl = 0 := by
    rw [hfl, ← coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, coeff_mk, if_pos rfl]
  set b : PowerSeries ℂ_[p] := PowerSeries.C ep * fl with hb
  have hb0 : constantCoeff b = 0 := by rw [hb, map_mul, hfl0, mul_zero]
  have hbS : HasSubst b := HasSubst.of_constantCoeff_zero' hb0
  have hhS : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set sg := Formalism.MainNotions.TaylorLogMetric.sgSer lam Λ with hsgdef
  have hsg0 : constantCoeff sg = 0 := by
    rw [hsg]; simp [Formalism.L2.Th1.B.sgStar, Formalism.L2.Th1.B.sigma]
  set E := Formalism.MainNotions.TaylorLogMetric.ePhi1 lam Λ C wq with hE
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl
  have hl0 : constantCoeff l = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hp2
  set q : PowerSeries ℂ_[p] := PowerSeries.C a⁻¹ * l with hq
  have hq0 : constantCoeff q = 0 := by rw [hq, map_mul, hl0, mul_zero]
  have hqS : HasSubst q := HasSubst.of_constantCoeff_zero' hq0

  have hA : PowerSeries.C ep * X * E = sg.subst b := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
        constantCoeff_X, mul_zero, zero_mul]
      exact (constantCoeff_subst_eq_zero hb0 _ hsg0).symm
    · rw [show PowerSeries.C ep * X * E = X * (PowerSeries.C ep * E) by ring, coeff_succ_X_mul, coeff_C_mul, hE]
      simp only [Formalism.MainNotions.TaylorLogMetric.ePhi1, coeff_mk, PowerSeries.algebraMap_eq]
      rw [← hep, ← mul_assoc, mul_inv_cancel₀ hep0, one_mul]

  have hB : PowerSeries.C ep * h * E.subst h = sg.subst q := by
    have e1 : (PowerSeries.C ep * X * E).subst h = PowerSeries.C ep * h * E.subst h := by
      rw [subst_mul hhS, subst_mul hhS, Formalism.L2.KerInert.MC.subst_C' hh0, subst_X hhS]
    have e2 : PowerSeries.subst h (PowerSeries.subst b sg) = sg.subst q := by
      rw [subst_comp_subst_apply hbS hhS, hb, subst_mul hhS, Formalism.L2.KerInert.MC.subst_C' hh0, hlog]
    rw [← e1, hA, e2]

  have hC : sg.subst q = PowerSeries.C a⁻¹ * X * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
    have hP0 : Formalism.L2.Th1.F.pOf g2 g3 = wpReg (shortW g2 g3) := by
      rw [Formalism.L2.KerInert.Sigma.wpReg_eq, (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.1,
        (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.1]
    have hsc : PowerSeries.C (a * ε) * sg =
        PowerSeries.rescale (a * ε) (Formalism.L2.Th1.B.sgStar s2 (wpReg (shortW g2 g3))) := by
      rw [hsg, (Formalism.L2.Th1.F.seriesScale ℂ_[p] g2 g3 (a * ε)).2.2.2.1, ← hP0]
      exact (Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf g2 g3) s2 (a * ε)).2
    have hεX : HasSubst ((a * ε) • (X : PowerSeries ℂ_[p])) := HasSubst.X'.smul' (a * ε)
    have hqq : PowerSeries.C (a * ε) * q = PowerSeries.C ε * l := by
      rw [hq, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have key : (PowerSeries.C (a * ε) * sg).subst q =
        (PowerSeries.rescale (a * ε) (Formalism.L2.Th1.B.sgStar s2 (wpReg (shortW g2 g3)))).subst q := by rw [hsc]
    rw [subst_mul hqS, Formalism.L2.KerInert.MC.subst_C' hq0, rescale_eq_subst, subst_comp_subst_apply hεX hqS,
      subst_smul hqS, subst_X hqS, smul_eq_C_mul, hqq, sig_at h5 g2 g3 s2 ε] at key
    have hc0 : (PowerSeries.C (a * ε) : PowerSeries ℂ_[p]) ≠ 0 := by
      intro h0; apply mul_ne_zero ha0 hε0; simpa using congrArg (coeff 0) h0
    refine mul_left_cancel₀ hc0 (key.trans ?_)
    rw [← mul_assoc, ← mul_assoc, ← map_mul]
    congr 3
    field_simp

  set hq' : PowerSeries ℂ_[p] := PowerSeries.mk fun n => coeff (n + 1) h with hhq
  have hX := X_mul_shift h hh0
  have hE2 : (PowerSeries.C (ep * a) * hq') * E.subst h = fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
    have hC' := hB.trans hC
    have e3 : PowerSeries.C ep * h = X * (PowerSeries.C ep * hq') := by
      rw [hhq]; nth_rewrite 1 [hX]; ring
    rw [e3, mul_assoc, show PowerSeries.C a⁻¹ * X * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) =
      X * (PowerSeries.C a⁻¹ * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε)) by ring] at hC'
    have hC2 := mul_left_cancel₀ (X_ne_zero (R := ℂ_[p])) hC'
    have e4 : (PowerSeries.C (ep * a) * hq') * E.subst h =
        PowerSeries.C a * (PowerSeries.C ep * hq' * E.subst h) := by
      rw [map_mul]; ring
    rw [e4, hC2, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
  refine ⟨PowerSeries.C (ep * a) * hq', fun n => ?_, ?_⟩
  · show ‖coeff n (PowerSeries.C (ep * a) * hq')‖ ≤ 1
    rw [coeff_C_mul, hhq, coeff_mk, norm_mul, hu1, one_mul]
    exact hhI (n + 1)
  · have hph0 := Formalism.L2.Th1.D.FAux.cc_phFF (K := ℂ_[p]) hp2 g2 g3 s2 ε
    set Uu := PowerSeries.C (ep * a) * hq' with hUu
    have hone : Uu * fExp (ι := Unit) (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) * E.subst h = 1 := by
      rw [mul_right_comm, hE2, ← fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph0) hph0, neg_add_cancel]
      exact Formalism.L2.Th1.B.Iso.fExp_zero
    have hcc : constantCoeff E ≠ 0 := by
      intro h0
      have := congrArg constantCoeff hone
      rw [map_mul, show constantCoeff (E.subst h) = 0 from constantCoeff_subst_eq_zero hh0 _ h0, mul_zero,
        map_one] at this
      exact zero_ne_one this
    have hinv : (E⁻¹).subst h * E.subst h = 1 := by
      rw [← subst_mul hhS, PowerSeries.inv_mul_cancel _ hcc, ← coe_substAlgHom hhS, map_one]
    calc (E⁻¹).subst h = (E⁻¹).subst h * (Uu * fExp (ι := Unit) (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) * E.subst h) := by
          rw [hone, mul_one]
      _ = Uu * fExp (ι := Unit) (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) * ((E⁻¹).subst h * E.subst h) := by ring
      _ = _ := by rw [hinv, mul_one]

end EPart

section Comparison₂

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

theorem g2_eq_pow_four_mul_g2_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) :
    L.g₂ = c ^ 4 * (Formalism.L2.Th1.F.scalePair L c hc).g₂ := by
  unfold PeriodPair.g₂
  rw [Formalism.L2.Th1.F.Homog.G_scale L c hc]
  field_simp

theorem g3_eq_pow_six_mul_g3_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) :
    L.g₃ = c ^ 6 * (Formalism.L2.Th1.F.scalePair L c hc).g₃ := by
  unfold PeriodPair.g₃
  rw [Formalism.L2.Th1.F.Homog.G_scale L c hc]
  field_simp

theorem s2_eq_sq_mul_s2_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) :
    Formalism.L2.Th1.F.s2 L = c ^ 2 * Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc) := by
  rw [Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale L c hc]
  field_simp

theorem modelTieS_of (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (hS2 : Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic) :
    Formalism.L2.KerInert.ModelTieS := by
  intro D cc δ B hcc hδ p _ h5 hin lam ι hι c hc g2 g3 ε s2 hLT n2 n3 nd hε hS C wq hCm hwq
  have hp2 : 2 ≤ p := by omega
  set L := B.L with hLdef
  have hlat : L.lattice.toAddSubgroup = lamOf D cc δ := B.lat
  have hΛ : B.tor.abelian₂ = lamOf D cc δ := rfl
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcc hδ L hlat
  have hs := hS2 D cc δ hcc hδ L hlat
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (lamOf D cc δ) L
    (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hlat)
  set a : ℂ_[p] := ι c with hadef
  have ha0 : a ≠ 0 := (map_ne_zero ι).2 hc
  set ε' : ℂ_[p] := a * (ε : ℂ_[p]) with hε'
  have j2 : ι L.g₂ = ε' ^ 4 * (g2 : ℂ_[p]) := by
    rw [g2_eq_pow_four_mul_g2_scalePair L c hc, map_mul, map_pow, hLT.1, hε']; ring
  have j3 : ι L.g₃ = ε' ^ 6 * (g3 : ℂ_[p]) := by
    rw [g3_eq_pow_six_mul_g3_scalePair L c hc, map_mul, map_pow, hLT.2.1, hε']; ring
  have js : ι (Formalism.L2.Th1.F.s2 L) = ε' ^ 2 * (s2 : ℂ_[p]) := by
    rw [s2_eq_sq_mul_s2_scalePair L c hc, map_mul, map_pow, hLT.2.2, hε']; ring
  have l2 : lam a2 = ε' ^ 4 * (g2 : ℂ_[p]) := (hι a2).symm.trans j2
  have l3 : lam a3 = ε' ^ 6 * (g3 : ℂ_[p]) := (hι a3).symm.trans j3
  have ls : lam s0 = ε' ^ 2 * (s2 : ℂ_[p]) := (hι s0).symm.trans js

  have hW0 : wModel lam B.tor.abelian₂ = Formalism.L2.Th1.A.shortW (ε' ^ 4 * (g2 : ℂ_[p])) (ε' ^ 6 * (g3 : ℂ_[p])) := by
    have e4 : lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (lamOf D cc δ)) / 4) = -(lam a2) / 4 := by
      have : -(Formalism.MainNotions.TaylorLogMetric.g2 (lamOf D cc δ)) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (lamOf D cc δ)) / 4) = -(lam a3) / 4 := by
      have : -(Formalism.MainNotions.TaylorLogMetric.g3 (lamOf D cc δ)) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hΛ]
    ext
    · rfl
    · rfl
    · rfl
    · show lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (lamOf D cc δ)) / 4) = -(ε' ^ 4 * (g2 : ℂ_[p])) / 4
      rw [e4, l2]
    · show lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (lamOf D cc δ)) / 4) = -(ε' ^ 6 * (g3 : ℂ_[p])) / 4
      rw [e6, l3]
  have hsg : sgSer lam B.tor.abelian₂ = Formalism.L2.Th1.B.sgStar ((a * (ε : ℂ_[p])) ^ 2 * (s2 : ℂ_[p]))
      (Formalism.L2.Th1.F.pOf ((a * (ε : ℂ_[p])) ^ 4 * (g2 : ℂ_[p])) ((a * (ε : ℂ_[p])) ^ 6 * (g3 : ℂ_[p]))) := by
    rw [hΛ, ← hlat, Formalism.L2.KerInert.Sigma.sgSer_eq lam L a2 a3 s0 rfl rfl rfl, l2, l3, ls]

  set ua : ℂ_[p]ˣ := Units.mk0 a ha0 with hua
  set C₂ := C * scaleVC ua with hC₂
  have hW2 : C₂ • Formalism.L2.Th1.A.shortW ((ε : ℂ_[p]) ^ 4 * (g2 : ℂ_[p])) ((ε : ℂ_[p]) ^ 6 * (g3 : ℂ_[p])) =
      C • wModel lam B.tor.abelian₂ := by
    rw [hC₂, mul_smul, scaleVC_smul, hW0, hε', hua, Units.val_mk0]
    congr 2 <;> ring
  obtain ⟨i1, i2, i3, -, -, hΔ1⟩ := hCm
  have hΔ : ‖(C • wModel lam B.tor.abelian₂).Δ‖ = 1 := by rw [hΔ1, norm_one]
  rw [← hW2] at i1 i2 i3 hΔ
  have hth : ∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS p (g2 : ℂ_[p]) (g3 : ℂ_[p]) (ε : ℂ_[p]))‖ ≤ 1 := by
    intro n
    have hm := Formalism.L2.Th1.D.FAux.thetaS_map (MaximalUnramifiedExtension p).subtype hp2 g2 g3 ε
    have e : PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS p (g2 : ℂ_[p]) (g3 : ℂ_[p]) (ε : ℂ_[p])) =
        (MaximalUnramifiedExtension p).subtype (PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS p g2 g3 ε)) := by
      rw [← PowerSeries.coeff_map, hm]; rfl
    rw [e]
    exact hS n
  obtain ⟨h, hh0, hhI, hh1, hlog⟩ := param h5 (g2 : ℂ_[p]) (g3 : ℂ_[p]) (ε : ℂ_[p]) hε n2 n3 nd hth C₂ i1 i2 i3 hΔ
  have hSΔ : ‖(Formalism.L2.Th1.A.shortW ((ε : ℂ_[p]) ^ 4 * (g2 : ℂ_[p])) ((ε : ℂ_[p]) ^ 6 * (g3 : ℂ_[p]))).Δ‖ = 1 := by
    rw [(Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).2.2.2]
    have : ((ε : ℂ_[p]) ^ 4 * (g2 : ℂ_[p])) ^ 3 - 27 * ((ε : ℂ_[p]) ^ 6 * (g3 : ℂ_[p])) ^ 2 =
        (ε : ℂ_[p]) ^ 12 * ((g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2) := by ring
    rw [this, norm_mul, norm_pow, show ‖(ε : ℂ_[p])‖ = 1 from hε, one_pow, one_mul]
    exact nd
  obtain ⟨hu1, -, -, -, -⟩ := Formalism.L2.KerInert.ModelP.vc_gen h5 _ (by simp [Formalism.L2.Th1.A.shortW])
    (by simp [Formalism.L2.Th1.A.shortW]) (by simp [Formalism.L2.Th1.A.shortW]) hSΔ C₂ i1 i2 i3 hΔ
  have hu2 := uinv_mul_scale C ua
  rw [← hC₂, hua, Units.val_mk0] at hu2
  have hunit : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * a‖ = 1 := by
    rw [← hu2, Units.val_inv_eq_inv_val, norm_inv, hu1, inv_one]
  have hfl : flog (C • wModel lam B.tor.abelian₂) wq = Formalism.L2.Th1.A.logSer (C • wModel lam B.tor.abelian₂) :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p _ wq hwq
  rw [hW2, hu2] at hlog
  have hlog' : PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (flog (C • wModel lam B.tor.abelian₂) wq).subst h =
      PowerSeries.C a⁻¹ * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
    rw [hfl, ← hlog, ← mul_assoc, ← map_mul]
    congr 2
    field_simp
  have hε0 : (ε : ℂ_[p]) ≠ 0 := by
    intro h0; have h1 : ‖(ε : ℂ_[p])‖ = 1 := hε; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨Uu, hUu, hE⟩ := ePartS h5 (g2 : ℂ_[p]) (g3 : ℂ_[p]) (ε : ℂ_[p]) (s2 : ℂ_[p]) a hε0 ha0 lam B.tor.abelian₂ C wq
    hsg hunit h hh0 hhI hlog'
  have hphL : Formalism.L2.Th1.Top.phL p g2 g3 s2 ε =
      Formalism.L2.Th1.D.phFF p (g2 : ℂ_[p]) (g3 : ℂ_[p]) (s2 : ℂ_[p]) (ε : ℂ_[p]) :=
    Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension p).subtype hp2 g2 g3 s2 ε
  refine ⟨?_, h, Uu, hh0, hhI, hh1, hlog', hUu, ?_⟩
  · rw [hphL]; exact Formalism.L2.Th1.D.FAux.cc_phFF hp2 _ _ _ _
  · rw [hE, hphL]; rfl

end Comparison₂

theorem model_series_algebraic : Formalism.L2.KerInert.ModelTieS :=
  modelTieS_of Formalism.L2.KerInert.Sigma.invAlg' Formalism.L2.KerInert.Sigma.secondEisensteinAlgebraic

end Formalism.L2.KerInert.MModelS
