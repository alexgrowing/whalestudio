import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace AnaSys

open Formalism.L2.Th1

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem lg0 : constantCoeff (A.logSer (curveL l L ι)) = 0 := (A.logSpec ℂ_[l] (curveL l L ι)).1

theorem lg1 : coeff 1 (A.logSer (curveL l L ι)) = 1 := (A.logSpec ℂ_[l] (curveL l L ι)).2.1

theorem lg_ne : A.logSer (curveL l L ι) ≠ 0 := by
  intro h
  have := lg1 l L ι
  rw [h] at this
  simp at this

theorem lgS : HasSubst (A.logSer (curveL l L ι)) := B.Ph.hs (lg0 l L ι)

theorem inU_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inU l L ι (fun z => f z * g z) = inU l L ι f * inU l L ι g := by
  unfold inU
  rw [F.Taylor.taylor0_mul hf hg, map_mul, subst_mul (lgS l L ι)]

theorem inU_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inU l L ι (fun z => f z + g z) = inU l L ι f + inU l L ι g := by
  unfold inU
  rw [F.Taylor.taylor0_add hf hg, map_add, subst_add (lgS l L ι)]

theorem inU_const (c : ℂ) : inU l L ι (fun _ => c) = C (ι c) := by
  unfold inU
  rw [F.Taylor.taylor0_const, map_C, subst_C]
  rfl

theorem inU_id : inU l L ι (fun z => z) = A.logSer (curveL l L ι) := by
  unfold inU
  rw [F.Taylor.taylor0_id, map_X, subst_X (lgS l L ι)]

theorem inU_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : inU l L ι f = inU l L ι g := by
  unfold inU
  rw [F.Taylor.taylor0_congr h]

theorem cc_inU (f : ℂ → ℂ) : constantCoeff (inU l L ι f) = ι (f 0) := by
  unfold inU
  rw [B.Ph.constantCoeff_psubst (lg0 l L ι), ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, F.TaylorSigmaUniqueness.constantCoeff_taylor0]
  rfl

def Rd (f : ℂ → ℂ) (S : PowerSeries ℂ_[l]) : Prop := AnalyticAt ℂ f 0 ∧ inU l L ι f = S

variable {l L ι}

theorem Rd.mul {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l L ι f S) (hg : Rd l L ι g T) :
    Rd l L ι (fun z => f z * g z) (S * T) :=
  ⟨hf.1.mul hg.1, by rw [inU_mul l L ι hf.1 hg.1, hf.2, hg.2]⟩

theorem Rd.add {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l L ι f S) (hg : Rd l L ι g T) :
    Rd l L ι (fun z => f z + g z) (S + T) :=
  ⟨hf.1.add hg.1, by rw [inU_add l L ι hf.1 hg.1, hf.2, hg.2]⟩

variable (l L ι)

theorem Rd.const (c : ℂ) : Rd l L ι (fun _ => c) (C (ι c)) := ⟨analyticAt_const, inU_const l L ι c⟩

theorem Rd.id : Rd l L ι (fun z => z) (A.logSer (curveL l L ι)) := ⟨analyticAt_id, inU_id l L ι⟩

theorem analytic_opU (x : ℂ) : AnalyticAt ℂ (F.opU L x (F.sgStar L)) 0 := by
  have h := (F.sgStarBasic L).1
  have : Differentiable ℂ (fun z => F.sgStar L (z + x) *
      Complex.exp (-(Real.pi : ℂ) * (z * (starRingEnd ℂ) x / (F.area L : ℂ))
        - (Real.pi : ℂ) * F.herm L x x / 2)) := by
    fun_prop
  exact this.analyticAt 0

theorem Rd.opU (x : ℂ) :
    Rd l L ι (F.opU L x (F.sgStar L)) (inU l L ι (F.opU L x (F.sgStar L))) :=
  ⟨analytic_opU L x, rfl⟩

theorem taylorSgStar : F.TaylorSgStar :=
  F.taylorSgStar_of (F.taylorSigma_of F.taylorRing F.taylorDeriv) F.taylorRing F.taylorExp F.sigmaEntire

theorem cc_phL : constantCoeff (phL l L ι) = 0 :=
  (B.phODef ℂ_[l] _ _ _ (lg0 l L ι) (lg1 l L ι)).1

theorem inU_sgStar : inU l L ι (F.sgStar L) = X * B.fExp (-(phL l L ι)) := by
  unfold inU phL
  rw [taylorSgStar L, B.Map.map_sgStar]
  exact (B.phODef ℂ_[l] _ _ _ (lg0 l L ι) (lg1 l L ι)).2

theorem fExp_cancel : B.fExp (phL l L ι) * B.fExp (-(phL l L ι)) = 1 :=
  B.ParO.fExp_mul_neg (cc_phL l L ι)

theorem cc_gT (t : ℂ) : constantCoeff (gT l L ι t) = ι (F.opU L t (F.sgStar L) 0) := by
  unfold gT
  rw [map_mul, cc_inU]
  have : constantCoeff (B.fExp (phL l L ι)) = 1 := B.constantCoeff_fExp (cc_phL l L ι)
  rw [this, one_mul]

theorem opU_zero_ne (t : ℂ) (ht : t ∉ L.lattice) : F.opU L t (F.sgStar L) 0 ≠ 0 := by
  unfold F.opU
  rw [zero_add]
  exact mul_ne_zero (fun h => ht (((F.sgStarBasic L).2.2.1 t).1 h)) (Complex.exp_ne_zero _)

theorem opU_zero_eq (t : ℂ) (ht : t ∈ L.lattice) : F.opU L t (F.sgStar L) 0 = 0 := by
  unfold F.opU
  rw [zero_add, ((F.sgStarBasic L).2.2.1 t).2 ht, zero_mul]

theorem gT_mem (t : ℂ) (ht : t ∈ L.lattice) : ∃ ε : ℂ_[l], ‖ε‖ = 1 ∧ gT l L ι t = C ε * X := by
  have hs : F.semiChar L t = 1 ∨ F.semiChar L t = -1 := by
    unfold F.semiChar
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hss : F.semiChar L t * F.semiChar L t = 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  have hfun : F.opU L t (F.sgStar L) = fun z => F.semiChar L t * F.sgStar L z := by
    funext z
    rw [← F.sgStarFixed L t z ht, ← mul_assoc, hss, one_mul]
  refine ⟨ι (F.semiChar L t), ?_, ?_⟩
  · rcases hs with h | h <;> rw [h] <;> simp
  · have hσ : Rd l L ι (F.sgStar L) (X * B.fExp (-(phL l L ι))) :=
      ⟨(F.sgStarBasic L).1.analyticAt 0, inU_sgStar l L ι⟩
    have h := ((Rd.const l L ι (F.semiChar L t)).mul hσ).2
    unfold gT
    rw [hfun, h]
    linear_combination (C (ι (F.semiChar L t)) * X) * fExp_cancel l L ι

theorem disc_ne : (curveL l L ι).Δ ≠ 0 := by
  rw [curveL, (A.shortInv ℂ_[l] _ _).2.2.2]
  intro h
  apply F.discNeZero L
  apply ι.injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
  exact h

theorem nonsing (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (disc_ne l L ι),
    WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (L.derivWeierstrassP_sq t ht)
  simp only [map_pow, map_sub, map_mul, map_ofNat] at h
  simp only [curveL, A.shortW]
  linear_combination h / 4

theorem ptOf_notMem (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι t ht) :=
  dif_pos ⟨ht, nonsing l L ι t ht⟩

theorem ptOf_mem (t : ℂ) (ht : t ∈ L.lattice) : ptOf l L ι t = 0 :=
  dif_neg (fun h => h.1 ht)

theorem ptOf_zero_iff (t : ℂ) : ptOf l L ι t = 0 ↔ t ∈ L.lattice := by
  constructor
  · intro h
    by_contra ht
    rw [ptOf_notMem l L ι t ht] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact ptOf_mem l L ι t

theorem px_ptOf (t : ℂ) (ht : t ∉ L.lattice) :
    px (curveL l L ι) (ptOf l L ι t) = ι (L.weierstrassP t) := by
  rw [ptOf_notMem l L ι t ht]
  rfl

theorem scaled_x_analytic_point (t : ℂ) (ht : t ∉ L.lattice) :
    x2 (curveL l L ι) (ptOf l L ι t) = X ^ 2 * xT (curveL l L ι) (ptOf l L ι t) := by
  rw [ptOf_notMem l L ι t ht]
  rfl

theorem scaled_x_analytic_point_lattice (t : ℂ) (ht : t ∈ L.lattice) :
    x2 (curveL l L ι) (ptOf l L ι t) = A.xS (curveL l L ι) := by
  rw [ptOf_mem l L ι t ht]
  rfl

theorem curveL_eq : curveL l L ι = (A.shortW L.g₂ L.g₃).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [curveL, A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wpBridge : WpBridge := by
  intro l _ L ι
  have h1 := F.curve_weierstrass_series_eq (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)).2.2.1
  rw [← h1, h2, curveL_eq]

theorem wpInU : X ^ 2 * (1 + A.logSer (curveL l L ι) ^ 2 * inU l L ι (L.weierstrassPExcept 0)) =
    A.logSer (curveL l L ι) ^ 2 * A.xS (curveL l L ι) := by
  have h := A.wpInU ℂ_[l] (curveL l L ι)
  have hb : (curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  rw [hb, wpBridge l L ι] at h
  have h' : X ^ 2 * (1 + A.logSer (curveL l L ι) ^ 2 *
      subst (A.logSer (curveL l L ι)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L))) =
      A.logSer (curveL l L ι) ^ 2 * A.xS (curveL l L ι) := by
    simpa using h
  exact h'

section Trans

open F.TaylorWp

variable (L : PeriodPair) (t : ℂ)

theorem ev_notMem (ht : t ∉ L.lattice) : ∀ᶠ z in nhds (0 : ℂ), z + t ∉ L.lattice :=
  (L.isClosed_lattice.isOpen_compl.preimage (continuous_add_const t)).mem_nhds (by simpa using ht)

theorem T_wp (ht : t ∉ L.lattice) :
    T (fun z => L.weierstrassP (z + t)) (F.taylor0 fun z => L.weierstrassP (z + t)) := by
  refine ⟨?_, rfl⟩
  have h1 : AnalyticAt ℂ L.weierstrassP (0 + t) := L.analyticOnNhd_weierstrassP _ (by simpa using ht)
  exact AnalyticAt.fun_comp h1 (analyticAt_id.add analyticAt_const)

theorem T_dwp (ht : t ∉ L.lattice) :
    T (fun z => L.derivWeierstrassP (z + t)) (F.taylor0 fun z => L.derivWeierstrassP (z + t)) := by
  refine ⟨?_, rfl⟩
  have h1 : AnalyticAt ℂ L.derivWeierstrassP (0 + t) :=
    L.analyticOnNhd_derivWeierstrassP _ (by simpa using ht)
  exact AnalyticAt.fun_comp h1 (analyticAt_id.add analyticAt_const)

theorem flowC (ht : t ∉ L.lattice) :
    A.IsFlow (A.curveS (A.shortW L.g₂ L.g₃)) (derivative ℂ)
      (F.taylor0 fun z => L.weierstrassP (z + t))
      (C (1 / 2 : ℂ) * F.taylor0 fun z => L.derivWeierstrassP (z + t)) := by
  have hr := F.taylorRing
  have hp := T_wp L t ht
  have hq := T_dwp L t ht
  have e1 : (F.taylor0 fun z => L.derivWeierstrassP (z + t)) *
        (F.taylor0 fun z => L.derivWeierstrassP (z + t)) =
      C (4 : ℂ) * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 3 +
        (C (-L.g₂) * (F.taylor0 fun z => L.weierstrassP (z + t)) + C (-L.g₃)) := by
    rw [← (T.mul hr hq hq).2, ← (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hp 3))
      (T.add hr (T.mul hr (T.const hr (-L.g₂)) hp) (T.const hr (-L.g₃)))).2]
    apply F.Taylor.taylor0_congr
    filter_upwards [ev_notMem L t ht] with z hz
    have := L.derivWeierstrassP_sq (z + t) hz
    linear_combination this
  have e2 : derivative ℂ (F.taylor0 fun z => L.weierstrassP (z + t)) =
      F.taylor0 fun z => L.derivWeierstrassP (z + t) := by
    rw [← F.Taylor.taylor0_deriv]
    congr 1
    funext z
    rw [deriv_comp_add_const, L.deriv_weierstrassP]
  have e3 : derivative ℂ (F.taylor0 fun z => L.derivWeierstrassP (z + t)) =
      C (6 : ℂ) * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 2 + C (-(L.g₂ / 2)) := by
    rw [← F.Taylor.taylor0_deriv, ← (T.add hr (T.mul hr (T.const hr 6) (T.pow hr hp 2))
      (T.const hr (-(L.g₂ / 2)))).2]
    apply F.Taylor.taylor0_congr
    filter_upwards [ev_notMem L t ht] with z hz
    rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
    ring
  have c2 : (C (1 / 2 : ℂ) : PowerSeries ℂ) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ →+* PowerSeries ℂ) 2, ← map_mul]; norm_num
  have k2 : (C (-L.g₂ / 4) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) * C (-L.g₂) := by
    rw [← map_mul, ← map_mul]; congr 1; ring
  have k3 : (C (-L.g₃ / 4) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) * C (-L.g₃) := by
    rw [← map_mul, ← map_mul]; congr 1; ring
  have k4 : (C (-(L.g₂ / 2)) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (-L.g₂) := by
    rw [← map_mul]; congr 1; ring
  have c4 : (C (4 : ℂ) : PowerSeries ℂ) = 4 := map_ofNat C 4
  have c6 : (C (6 : ℂ) : PowerSeries ℂ) = 6 := map_ofNat C 6
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW, WeierstrassCurve.map, map_zero]
    rw [k2, k3]
    rw [c4] at e1
    linear_combination (C (1 / 2 : ℂ) * C (1 / 2 : ℂ)) * e1 +
      ((F.taylor0 fun z => L.weierstrassP (z + t)) ^ 3 * (C (1 / 2 : ℂ) * 2 + 1)) * c2
  · simp only [A.shortW, WeierstrassCurve.map, map_zero]
    linear_combination e2 - (F.taylor0 fun z => L.derivWeierstrassP (z + t)) * c2
  · simp only [A.shortW, WeierstrassCurve.map, map_zero]
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, e3, k2, k4, c6]
    linear_combination (3 * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 2) * c2

theorem transC (ht : t ∉ L.lattice) :
    (A.xPlus (A.shortW L.g₂ L.g₃) (L.weierstrassP t) (L.derivWeierstrassP t / 2)).subst
        (A.expSer (A.shortW L.g₂ L.g₃)) = F.taylor0 fun z => L.weierstrassP (z + t) := by
  have heq : (A.shortW L.g₂ L.g₃).toAffine.Equation (L.weierstrassP t) (L.derivWeierstrassP t / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (L.derivWeierstrassP_sq t ht) / 4
  have he0 : constantCoeff (A.expSer (A.shortW L.g₂ L.g₃)) = 0 := (A.expSpec ℂ _).1
  have hf := (A.plusFlow ℂ (A.shortW L.g₂ L.g₃) _ _ heq)
  refine (A.flowUniqueZ ℂ (A.shortW L.g₂ L.g₃) _ _ _ _ (A.plusZ ℂ _ _ _ heq).1 (flowC L t ht) ?_ ?_).1
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.1, F.TaylorSigmaUniqueness.constantCoeff_taylor0, zero_add]
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.2, map_mul, F.TaylorSigmaUniqueness.constantCoeff_taylor0, zero_add,
      constantCoeff_C]
    ring

end Trans

theorem transWpBridge : TransWpBridge := by
  intro l _ L ι t ht
  have hz := A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)
  have hp := (A.plusMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃) (L.weierstrassP t)
    (L.derivWeierstrassP t / 2)).2.1
  have he := A.expSpec ℂ_[l] (curveL l L ι)
  unfold inU
  rw [← transC L t ht, B.Map.map_psubst' _ (A.expSpec ℂ _).1, hz.2.1, hp, ← curveL_eq,
    subst_comp_subst_apply (B.Ph.hs he.1) (lgS l L ι), he.2.2.2.1, X_subst, ptOf_notMem l L ι t ht]
  simp only [xT, px, py, RingEquiv.coe_toRingHom, map_div₀, map_ofNat]

theorem prod_notMem (hT : TransWpBridge) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    X ^ 2 * (gT l L ι (P + Q) * gT l L ι (P - Q)) =
      C (constantCoeff (gT l L ι Q) ^ 2) *
        (C (px (curveL l L ι) (ptOf l L ι Q)) * X ^ 2 - x2 (curveL l L ι) (ptOf l L ι P)) *
        gT l L ι P ^ 2 := by
  have hop : {z : ℂ | z + P ∉ L.lattice} ∈ nhds (0 : ℂ) :=
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_add_const P)).mem_nhds (by simpa using hP)
  have hev : (fun z => F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (L.weierstrassP Q + (-1) * L.weierstrassP (z + P)) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [hop] with z hz
    rw [F.translateProduct L P Q z hQ hz]
    ring
  have hwp : Rd l L ι (fun z => L.weierstrassP (z + P)) (xT (curveL l L ι) (ptOf l L ι P)) := by
    refine ⟨?_, hT l L ι P hP⟩
    have h1 : AnalyticAt ℂ L.weierstrassP (0 + P) := L.analyticOnNhd_weierstrassP _ (by simpa using hP)
    exact AnalyticAt.fun_comp h1 (analyticAt_id.add analyticAt_const)
  have hl := ((Rd.opU l L ι (P + Q)).mul (Rd.opU l L ι (P - Q))).2
  have hr := (((Rd.const l L ι (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    ((Rd.const l L ι (L.weierstrassP Q)).add ((Rd.const l L ι (-1)).mul hwp))).mul
    ((Rd.opU l L ι P).mul (Rd.opU l L ι P))).2
  have key := hl.symm.trans ((inU_congr l L ι hev).trans hr)
  simp only [map_pow, map_neg, map_one] at key
  rw [cc_gT, px_ptOf l L ι Q hQ, scaled_x_analytic_point l L ι P hP]
  unfold gT
  simp only [map_pow]
  linear_combination (X ^ 2 * B.fExp (phL l L ι) ^ 2) * key

theorem prod_mem (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∈ L.lattice) :
    X ^ 2 * (gT l L ι (P + Q) * gT l L ι (P - Q)) =
      C (constantCoeff (gT l L ι Q) ^ 2) *
        (C (px (curveL l L ι) (ptOf l L ι Q)) * X ^ 2 - x2 (curveL l L ι) (ptOf l L ι P)) *
        gT l L ι P ^ 2 := by
  have hev : (fun z => (z * z) *
        (F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z)) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 *
          (L.weierstrassP Q * (z * z) + (-1) * (1 + (z * z) * L.weierstrassPExcept 0 z)) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
    by_cases h0 : z = 0
    · subst h0
      rw [opU_zero_eq L P hP]
      ring
    · have hzL : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
      have hzP : z + P ∉ L.lattice := fun h => hzL (by simpa using L.lattice.sub_mem h hP)
      rw [F.translateProduct L P Q z hQ hzP, L.weierstrassP_add_coe z ⟨P, hP⟩,
        ← L.weierstrassPExcept_add (0 : L.lattice) z]
      simp only [ZeroMemClass.coe_zero, sub_zero]
      field_simp
      ring
  have hz2 : Rd l L ι (fun z => z * z) _ := (Rd.id l L ι).mul (Rd.id l L ι)
  have hex : Rd l L ι (L.weierstrassPExcept 0) (inU l L ι (L.weierstrassPExcept 0)) :=
    ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
  have hl := (hz2.mul ((Rd.opU l L ι (P + Q)).mul (Rd.opU l L ι (P - Q)))).2
  have hr := (((Rd.const l L ι (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    (((Rd.const l L ι (L.weierstrassP Q)).mul hz2).add
      ((Rd.const l L ι (-1)).mul ((Rd.const l L ι 1).add (hz2.mul hex))))).mul
    ((Rd.opU l L ι P).mul (Rd.opU l L ι P))).2
  have key := hl.symm.trans ((inU_congr l L ι hev).trans hr)
  simp only [map_pow, map_neg, map_one] at key
  have hw := wpInU l L ι
  rw [cc_gT, px_ptOf l L ι Q hQ, scaled_x_analytic_point_lattice l L ι P hP]
  unfold gT
  simp only [map_pow]
  apply mul_left_cancel₀ (pow_ne_zero 2 (lg_ne l L ι))
  linear_combination (X ^ 2 * B.fExp (phL l L ι) ^ 2) * key -
    (C (ι (F.opU L Q (F.sgStar L) 0)) ^ 2 * B.fExp (phL l L ι) ^ 2 *
      inU l L ι (F.opU L P (F.sgStar L)) ^ 2) * hw

end AnaSys

theorem PtOfZero_of : PtOfZero := fun l _ L ι t => AnaSys.ptOf_zero_iff l L ι t

theorem WpBridge_of : WpBridge := AnaSys.wpBridge

theorem AnalyticSys_of (hT : TransWpBridge) : AnalyticSys := by
  intro l _ L ι π hπ
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hπ] at ht
    exact AnaSys.gT_mem l L ι t ((AnaSys.ptOf_zero_iff l L ι t).1 ht)
  · intro t ht
    rw [hπ] at ht
    rw [AnaSys.cc_gT]
    intro h
    have h' : Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0 = 0 := by
      apply ι.injective
      rw [h, map_zero]
    exact AnaSys.opU_zero_ne L t (fun hm => ht ((AnaSys.ptOf_zero_iff l L ι t).2 hm)) h'
  · intro P Q hQ
    rw [hπ] at hQ
    have hQ' : Q ∉ L.lattice := fun hm => hQ ((AnaSys.ptOf_zero_iff l L ι Q).2 hm)
    rw [hπ Q, hπ P]
    by_cases hP : P ∈ L.lattice
    · exact AnaSys.prod_mem l L ι P Q hQ' hP
    · exact AnaSys.prod_notMem l L ι hT P Q hQ' hP

theorem TransWpBridge_of : TransWpBridge := AnaSys.transWpBridge

theorem analytic_translate_system : AnalyticSys := AnalyticSys_of TransWpBridge_of

end Formalism.L2.Th1.E
