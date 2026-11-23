import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftPtsInt

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace AnaSysW

open Formalism.L2.Th1

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

theorem lg0 : constantCoeff (A.logSer W) = 0 := by
  first
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [A.logSer, A.integ, PowerSeries.coeff_mk])
  | (simp only [A.logSer, A.integ]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; simp)

theorem lg1 : coeff 1 (A.logSer W) = 1 := by
  first
  | (simp only [A.logSer, A.integ, PowerSeries.coeff_mk]; simp [A.om, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit])
  | (simp [A.logSer, A.integ, A.om, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply])

theorem lg_ne : A.logSer W ≠ 0 := by
  intro h
  have h1 := lg1 (W := W)
  rw [h] at h1
  simp at h1

theorem lgS : HasSubst (A.logSer W) := by
  first
  | exact HasSubst.of_constantCoeff_zero' (lg0 (W := W))
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' (lg0 (W := W))
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (lg0 (W := W))

theorem inW_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inW l ι W (fun z => f z * g z) = inW l ι W f * inW l ι W g := by
  have h := (F.taylorRing.1 f g hf hg).2
  unfold inW
  rw [h, map_mul]
  first
  | exact PowerSeries.subst_mul (lgS (W := W)) _ _
  | exact PowerSeries.subst_mul (ha := lgS (W := W)) _ _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_mul _ _ _)
  | simp [PowerSeries.subst_mul, lgS]

theorem inW_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    inW l ι W (fun z => f z + g z) = inW l ι W f + inW l ι W g := by
  have h := (F.taylorRing.1 f g hf hg).1
  unfold inW
  rw [h, map_add]
  first
  | exact PowerSeries.subst_add (lgS (W := W)) _ _
  | exact PowerSeries.subst_add (ha := lgS (W := W)) _ _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact map_add _ _ _)
  | simp [PowerSeries.subst_add, lgS]

theorem inW_const (c : ℂ) : inW l ι W (fun _ => c) = C (ι c) := by
  unfold inW
  rw [F.taylorRing.2.1 c, PowerSeries.map_C]
  first
  | exact PowerSeries.subst_C (lgS (W := W)) _
  | exact PowerSeries.subst_C (ha := lgS (W := W)) _
  | (rw [← PowerSeries.coe_substAlgHom (lgS (W := W))]; exact (PowerSeries.substAlgHom _).commutes _)
  | simp [PowerSeries.subst_C, lgS]

theorem inW_id : inW l ι W (fun z => z) = A.logSer W := by
  unfold inW
  rw [F.taylorRing.2.2.1, PowerSeries.map_X]
  first
  | exact PowerSeries.subst_X (lgS (W := W))
  | exact PowerSeries.subst_X (ha := lgS (W := W))
  | simp [PowerSeries.subst_X, lgS]

theorem inW_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : inW l ι W f = inW l ι W g := by
  unfold inW
  rw [F.taylorRing.2.2.2 f g h]

theorem cc_inW (f : ℂ → ℂ) : constantCoeff (inW l ι W f) = ι (f 0) := by
  unfold inW
  have hS : constantCoeff (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)) = ι (f 0) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp [F.taylor0, PowerSeries.coeff_mk]
  have ha := lgS (W := W)
  have h0 := lg0 (W := W)
  have hX : PowerSeries.subst (A.logSer W) (X : PowerSeries ℂ_[l]) = A.logSer W := by
    first
    | exact PowerSeries.subst_X ha
    | exact PowerSeries.subst_X (ha := ha)
    | simp [PowerSeries.subst_X, ha]
  have hC : ∀ c : ℂ_[l], PowerSeries.subst (A.logSer W) (C c : PowerSeries ℂ_[l]) = C c := by
    intro c
    first
    | exact PowerSeries.subst_C ha c
    | exact PowerSeries.subst_C (ha := ha) c
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact (PowerSeries.substAlgHom ha).commutes c)
    | simp [PowerSeries.subst_C, ha]
  rw [PowerSeries.eq_shift_mul_X_add_const (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 f)),
    ← PowerSeries.coe_substAlgHom ha, map_add, map_mul, PowerSeries.coe_substAlgHom, hX, hC]
  simp [h0, hS]

def Rd (f : ℂ → ℂ) (S : PowerSeries ℂ_[l]) : Prop := AnalyticAt ℂ f 0 ∧ inW l ι W f = S

variable {l ι W}

theorem Rd.mul {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l ι W f S) (hg : Rd l ι W g T) :
    Rd l ι W (fun z => f z * g z) (S * T) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  rw [inW_mul (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]

theorem Rd.add {f g : ℂ → ℂ} {S T : PowerSeries ℂ_[l]} (hf : Rd l ι W f S) (hg : Rd l ι W g T) :
    Rd l ι W (fun z => f z + g z) (S + T) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  rw [inW_add (l := l) (ι := ι) (W := W) hf.1 hg.1, hf.2, hg.2]

variable (l ι W)

theorem Rd.const (c : ℂ) : Rd l ι W (fun _ => c) (C (ι c)) := by
  exact ⟨analyticAt_const, inW_const (l := l) (ι := ι) (W := W) c⟩

theorem Rd.id : Rd l ι W (fun z => z) (A.logSer W) := by
  refine ⟨?_, inW_id (l := l) (ι := ι) (W := W)⟩
  first | exact analyticAt_id | fun_prop

theorem Rd.opU (x : ℂ) :
    Rd l ι W (F.opU L x (F.sgStar L)) (inW l ι W (F.opU L x (F.sgStar L))) := by
  have hs : Differentiable ℂ (F.wSigma L) := F.sigmaEntire L
  have hd : Differentiable ℂ (F.opU L x (F.sgStar L)) := by
    unfold F.opU F.sgStar F.herm
    fun_prop
  refine ⟨?_, rfl⟩
  first
  | exact hd.analyticAt 0
  | exact Differentiable.analyticAt hd 0

theorem cc_phW : constantCoeff (phW l L ι W) = 0 := by
  unfold phW
  exact B.Ph.constantCoeff_phO _ _ (lg0 (W := W)) (lg1 (W := W))

theorem inW_sgStar : inW l ι W (F.sgStar L) = X * B.fExp (-(phW l L ι W)) := by
  have hT : F.taylor0 (F.sgStar L) = B.sgStar (F.s2 L) (F.pSeries L) := AnaSys.taylorSgStar L
  have hM := (B.Map.baseChangeCompatible ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (F.s2 L) 0 0 (F.pSeries L) 0
    PowerSeries.X 0 (by simp) (by simp) (by simp)).2.1
  have hD := (B.Ph.logSigmaPullbackSpec ℂ_[l] (ι (F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L))
    (A.logSer W) (lg0 (W := W)) (lg1 (W := W))).2
  unfold inW phW
  rw [hT, hM]
  exact hD

theorem fExp_cancel : B.fExp (phW l L ι W) * B.fExp (-(phW l L ι W)) = 1 := by
  have h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0 := cc_phW (l := l) (L := L) (ι := ι) (W := W)
  have h2 : MvPowerSeries.constantCoeff (-(phW l L ι W)) = 0 := by rw [map_neg, h1, neg_zero]
  rw [← B.fExp_add h1 h2, add_neg_cancel]
  have h0 : MvPowerSeries.constantCoeff (0 : PowerSeries ℂ_[l]) = 0 := map_zero _
  have e : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) = B.fExp (0 : PowerSeries ℂ_[l]) * B.fExp (0 : PowerSeries ℂ_[l]) := by
    have e' := B.fExp_add h0 h0
    rw [add_zero] at e'
    exact e'
  have c := B.constantCoeff_fExp h0
  have hne : (B.fExp (0 : PowerSeries ℂ_[l]) : PowerSeries ℂ_[l]) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at c
    exact zero_ne_one c
  exact mul_left_cancel₀ hne (e.symm.trans (mul_one _).symm)

theorem cc_gW (t : ℂ) : constantCoeff (gW l L ι W t) = ι (F.opU L t (F.sgStar L) 0) := by
  have h1 : MvPowerSeries.constantCoeff (phW l L ι W) = 0 := cc_phW (l := l) (L := L) (ι := ι) (W := W)
  have hc : constantCoeff (B.fExp (phW l L ι W)) = 1 := B.constantCoeff_fExp h1
  unfold gW
  rw [map_mul, hc, one_mul, cc_inW]

theorem gW_mem (t : ℂ) (ht : t ∈ L.lattice) : ∃ ε : ℂ_[l], ‖ε‖ = 1 ∧ gW l L ι W t = C ε * X := by
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
  · have hσ : Rd l ι W (F.sgStar L) (X * B.fExp (-(phW l L ι W))) :=
      ⟨(F.sgStarBasic L).1.analyticAt 0, inW_sgStar l L ι W⟩
    have h := ((Rd.const l ι W (F.semiChar L t)).mul hσ).2
    unfold gW
    rw [hfun, h]
    linear_combination (C (ι (F.semiChar L t)) * X) * fExp_cancel l L ι W

abbrev xc (t : ℂ) : ℂ_[l] := ι (L.weierstrassP t) - W.b₂ / 12

abbrev yc (t : ℂ) : ℂ_[l] :=
  (ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2

variable {l L ι W}

theorem disc_ne (hU : Unif l L ι W) : W.Δ ≠ 0 := by
  intro hΔ
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃] at h1 h2
  have hc := WeierstrassCurve.c_relation W
  rw [hΔ] at hc
  apply F.discNeZero L
  apply ι.injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
  rw [← h1, ← h2]
  linear_combination (-1 / 1728) * hc

theorem nonsing (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    W.toAffine.Nonsingular (xc l L ι W t) (yc l L ι W t) := by
  have hΔ := disc_ne hU
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h1 h2
  have hn : (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact AnaSys.nonsing (l := l) (L := L) (ι := ι) t ht
    | exact AddThm.nonsing (l := l) (L := L) (ι := ι) t ht
  have he : (curveL l L ι).toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact hn.1
    | exact hn.left
    | exact (WeierstrassCurve.Affine.nonsingular_iff' _ _).1 hn |>.1
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [curveL, A.shortW] at he
  have heq : W.toAffine.Equation (xc l L ι W t) (yc l L ι W t) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [xc, yc, WeierstrassCurve.b₂]
    linear_combination he + (ι (L.weierstrassP t) / 4) * h1 + (1 / 4) * h2
  first
  | exact WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero heq hΔ
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq)
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp heq)

theorem ptW_notMem (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    ptW l L ι W t = .some _ _ (nonsing hU t ht) := by
  unfold ptW
  exact dif_pos ⟨ht, nonsing hU t ht⟩

variable (l L ι W)

theorem ptW_mem (t : ℂ) (ht : t ∈ L.lattice) : ptW l L ι W t = 0 := by
  unfold ptW
  exact dif_neg (fun h => h.1 ht)

variable {l L ι W}

theorem ptW_zero_iff (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W t = 0 ↔ t ∈ L.lattice := by
  constructor
  · intro h
    by_contra ht
    rw [ptW_notMem hU t ht] at h
    first | exact WeierstrassCurve.Affine.Point.some_ne_zero _ h | simp at h | cases h | exact nomatch h
  · intro ht
    exact ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht

theorem px_ptW (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    px W (ptW l L ι W t) = xc l L ι W t := by
  rw [ptW_notMem hU t ht]
  first | rfl | simp [px]

theorem scaled_x_model_point (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    x2 W (ptW l L ι W t) = X ^ 2 * xT W (ptW l L ι W t) := by
  rw [ptW_notMem hU t ht]
  first | rfl | simp [x2, xT, px, py]

variable (l L ι W)

theorem scaled_x_model_point_lattice (t : ℂ) (ht : t ∈ L.lattice) : x2 W (ptW l L ι W t) = A.xS W := by
  rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht]
  first | rfl | simp [x2]

def W0 : WeierstrassCurve ℂ := W.map (ι.symm : ℂ_[l] →+* ℂ)

theorem lattice_model_map : (W0 l ι W).map (ι : ℂ →+* ℂ_[l]) = W := by
  first
  | (ext <;> simp [W0])
  | (simp only [W0, WeierstrassCurve.map_map]; simp)

variable {l L ι W}

theorem lattice_model_g2 (hU : Unif l L ι W) : A.g₂ (W0 l ι W) = L.g₂ := by
  apply ι.injective
  have h := hU.1
  first
  | (simp only [A.g₂] at h ⊢; simp only [W0, WeierstrassCurve.map_c₄, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₂, W0, map_div₀] at h ⊢; exact h)

theorem lattice_model_g3 (hU : Unif l L ι W) : A.g₃ (W0 l ι W) = L.g₃ := by
  apply ι.injective
  have h := hU.2
  first
  | (simp only [A.g₃] at h ⊢; simp only [W0, WeierstrassCurve.map_c₆, map_div₀, map_neg, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₃, W0, map_div₀] at h ⊢; exact h)

theorem wpBridge (hU : Unif l L ι W) :
    A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curve_weierstrass_series_eq (W0 l ι W) L (lattice_model_g2 hU) (lattice_model_g3 hU)
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)).2.2.1
  rw [← h1, h2, lattice_model_map]

theorem wpInW (hU : Unif l L ι W) :
    X ^ 2 * (1 + A.logSer W ^ 2 * inW l ι W (L.weierstrassPExcept 0)) =
      A.logSer W ^ 2 * (A.xS W + C (W.b₂ / 12) * X ^ 2) := by
  have h := A.wpInU ℂ_[l] W
  rw [wpBridge hU] at h
  exact h

section Trans

open F.TaylorWp

variable (L : PeriodPair) (V : WeierstrassCurve ℂ) (t : ℂ)

def xf : ℂ → ℂ := fun z => L.weierstrassP (z + t) + -(V.b₂ / 12)

def yf : ℂ → ℂ := fun z => (1 / 2) * (L.derivWeierstrassP (z + t) + (-V.a₁ * xf L V t z + -V.a₃))

theorem T_xf (ht : t ∉ L.lattice) : T (xf L V t) (F.taylor0 (xf L V t)) := by
  refine ⟨?_, rfl⟩
  have h : AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0 := by
    first
    | exact (AnaSys.T_wp ht).1
    | exact (AnaSys.T_wp (L := L) (t := t) ht).1
    | exact (AnaSys.T_wp L t ht).1
  exact h.add analyticAt_const

theorem T_yf (ht : t ∉ L.lattice) : T (yf L V t) (F.taylor0 (yf L V t)) := by
  refine ⟨?_, rfl⟩
  have h : AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0 := by
    first
    | exact (AnaSys.T_dwp ht).1
    | exact (AnaSys.T_dwp (L := L) (t := t) ht).1
    | exact (AnaSys.T_dwp L t ht).1
  have hx := (T_xf L V t ht).1
  exact analyticAt_const.mul (h.add ((analyticAt_const.mul hx).add analyticAt_const))

theorem hasDeriv_xf (z : ℂ) (hz : z + t ∉ L.lattice) :
    HasDerivAt (xf L V t) (L.derivWeierstrassP (z + t)) z := by
  have h := F.PDeriv.hasDerivAt_P L hz
  first
  | exact (h.comp_add_const z t).add_const _
  | exact (HasDerivAt.comp_add_const z t h).add_const _

theorem hasDeriv_yf (z : ℂ) (hz : z + t ∉ L.lattice) :
    HasDerivAt (yf L V t) ((1 / 2) * ((6 * L.weierstrassP (z + t) ^ 2 - L.g₂ / 2) +
      -V.a₁ * L.derivWeierstrassP (z + t))) z := by
  have h2 : HasDerivAt (fun w => L.derivWeierstrassP (w + t)) (6 * L.weierstrassP (z + t) ^ 2 - L.g₂ / 2) z := by
    first
    | exact (F.pSecond L (z + t) hz).comp_add_const z t
    | exact HasDerivAt.comp_add_const z t (F.pSecond L (z + t) hz)
  have hx := hasDeriv_xf L V t z hz
  exact (h2.add ((hx.const_mul (-V.a₁)).add_const (-V.a₃))).const_mul (1 / 2)

variable {L V}

theorem flowC (h2 : A.g₂ V = L.g₂) (h3 : A.g₃ V = L.g₃) (ht : t ∉ L.lattice) :
    A.IsFlow (A.curveS V) (derivative ℂ) (F.taylor0 (xf L V t)) (F.taylor0 (yf L V t)) := by
  have hr := F.taylorRing
  have hx := T_xf L V t ht
  have hy := T_yf L V t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    have hl := (T.add hr (T.add hr (T.pow hr hy 2) (T.mul hr (T.mul hr (T.const hr V.a₁) hx) hy))
      (T.mul hr (T.const hr V.a₃) hy)).2
    have hq := (T.add hr (T.add hr (T.add hr (T.pow hr hx 3) (T.mul hr (T.const hr V.a₂) (T.pow hr hx 2)))
      (T.mul hr (T.const hr V.a₄) hx)) (T.const hr V.a₆)).2
    refine hl.symm.trans (Eq.trans ?_ hq)
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    have h := L.derivWeierstrassP_sq (z + t) hz
    rw [← h2, ← h3] at h
    simp only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢
    linear_combination h / 4
  · have hq := (T.add hr (T.add hr (T.mul hr (T.const hr 2) hy) (T.mul hr (T.const hr V.a₁) hx))
      (T.const hr V.a₃)).2
    have c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2 := map_ofNat C 2
    rw [c2] at hq
    rw [← F.Taylor.taylor0_deriv]
    refine Eq.trans ?_ hq
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    rw [(hasDeriv_xf L V t z hz).deriv]
    simp only [yf]
    ring
  · have hq := (T.add hr (T.add hr (T.add hr (T.mul hr (T.const hr 3) (T.pow hr hx 2))
      (T.mul hr (T.mul hr (T.const hr 2) (T.const hr V.a₂)) hx)) (T.const hr V.a₄))
      (T.mul hr (T.const hr (-V.a₁)) hy)).2
    have c2 : (C (2 : ℂ) : PowerSeries ℂ) = 2 := map_ofNat C 2
    have c3 : (C (3 : ℂ) : PowerSeries ℂ) = 3 := map_ofNat C 3
    rw [c2, c3, map_neg, neg_mul, ← sub_eq_add_neg] at hq
    rw [← F.Taylor.taylor0_deriv]
    refine Eq.trans ?_ hq
    apply F.Taylor.taylor0_congr
    filter_upwards [AnaSys.ev_notMem L t ht] with z hz
    rw [(hasDeriv_yf L V t z hz).deriv, ← h2]
    simp only [xf, yf, A.g₂, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring

theorem transC (h2 : A.g₂ V = L.g₂) (h3 : A.g₃ V = L.g₃) (ht : t ∉ L.lattice) :
    (A.xPlus V (xf L V t 0) (yf L V t 0)).subst (A.expSer V) = F.taylor0 (xf L V t) := by
  have hfl := flowC t h2 h3 ht
  have heq : V.toAffine.Equation (xf L V t 0) (yf L V t 0) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have h := L.derivWeierstrassP_sq (0 + t) (by simpa using ht)
    rw [← h2, ← h3] at h
    simp only [xf, yf, A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢
    linear_combination h / 4
  have he0 : constantCoeff (A.expSer V) = 0 := (A.expSpec ℂ _).1
  have hf := (A.plusFlow ℂ V _ _ heq)
  refine (A.flowUniqueZ ℂ V _ _ _ _ (A.plusZ ℂ _ _ _ heq).1 hfl ?_ ?_).1
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.1, F.TaylorSigmaUniqueness.constantCoeff_taylor0]
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.2, F.TaylorSigmaUniqueness.constantCoeff_taylor0]

end Trans

theorem map_analytic_x_at_zero (t : ℂ) : ι (xf L (W0 l ι W) t 0) = xc l L ι W t := by
  first
  | (simp only [xf, xc, W0, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)
  | (simp [xf, xc, W0, map_div₀, sub_eq_add_neg])

theorem map_analytic_y_at_zero (t : ℂ) : ι (yf L (W0 l ι W) t 0) = yc l L ι W t := by
  first
  | (simp only [yf, yc, xf, W0, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, WeierstrassCurve.map_b₂, zero_add, map_add, map_neg, map_mul, map_div₀, map_one, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; ring)
  | (simp [yf, yc, xf, W0, map_div₀]; ring)

theorem transW (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    inW l ι W (xf L (W0 l ι W) t) = xT W (ptW l L ι W t) := by
  have hz := A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)
  have hp := (A.plusMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W) (xf L (W0 l ι W) t 0)
    (yf L (W0 l ι W) t 0)).2.1
  have he := A.expSpec ℂ_[l] W
  unfold inW
  rw [← transC t (lattice_model_g2 hU) (lattice_model_g3 hU) ht, B.Map.map_psubst' _ (A.expSpec ℂ _).1, hz.2.1, hp, lattice_model_map,
    subst_comp_subst_apply (B.Ph.hs he.1) (lgS l W), he.2.2.2.1, X_subst, ptW_notMem hU t ht]
  simp only [xT, px, py, RingEquiv.coe_toRingHom, map_analytic_x_at_zero, map_analytic_y_at_zero]

theorem prod_notMem (hU : Unif l L ι W) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    X ^ 2 * (gW l L ι W (P + Q) * gW l L ι W (P - Q)) =
      C (constantCoeff (gW l L ι W Q) ^ 2) *
        (C (px W (ptW l L ι W Q)) * X ^ 2 - x2 W (ptW l L ι W P)) * gW l L ι W P ^ 2 := by
  have hev : (fun z => F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (xf L (W0 l ι W) Q 0 + (-1) * xf L (W0 l ι W) P z) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [AnaSys.ev_notMem L P hP] with z hz
    rw [F.translateProduct L P Q z hQ hz]
    simp only [xf, zero_add]
    ring
  have hwp : Rd l ι W (xf L (W0 l ι W) P) (xT W (ptW l L ι W P)) :=
    ⟨(T_xf L (W0 l ι W) P hP).1, transW hU P hP⟩
  have hl := ((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q))).2
  have hr := (((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    ((Rd.const l ι W (xf L (W0 l ι W) Q 0)).add ((Rd.const l ι W (-1)).mul hwp))).mul
    ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2
  have key := hl.symm.trans ((inW_congr l ι W hev).trans hr)
  simp only [map_pow, map_neg, map_one, map_analytic_x_at_zero] at key
  rw [cc_gW, px_ptW hU Q hQ, scaled_x_model_point hU P hP]
  unfold gW
  simp only [map_pow]
  linear_combination (X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key

theorem prod_mem (hU : Unif l L ι W) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∈ L.lattice) :
    X ^ 2 * (gW l L ι W (P + Q) * gW l L ι W (P - Q)) =
      C (constantCoeff (gW l L ι W Q) ^ 2) *
        (C (px W (ptW l L ι W Q)) * X ^ 2 - x2 W (ptW l L ι W P)) * gW l L ι W P ^ 2 := by
  have hev : (fun z => (z * z) *
        (F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z)) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 *
          (L.weierstrassP Q * (z * z) + (-1) * (1 + (z * z) * L.weierstrassPExcept 0 z)) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
    by_cases h0 : z = 0
    · subst h0
      rw [AnaSys.opU_zero_eq L P hP]
      ring
    · have hzL : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
      have hzP : z + P ∉ L.lattice := fun h => hzL (by simpa using L.lattice.sub_mem h hP)
      rw [F.translateProduct L P Q z hQ hzP, L.weierstrassP_add_coe z ⟨P, hP⟩,
        ← L.weierstrassPExcept_add (0 : L.lattice) z]
      simp only [ZeroMemClass.coe_zero, sub_zero]
      field_simp
      ring
  have hz2 : Rd l ι W (fun z => z * z) _ := (Rd.id l ι W).mul (Rd.id l ι W)
  have hex : Rd l ι W (L.weierstrassPExcept 0) (inW l ι W (L.weierstrassPExcept 0)) :=
    ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
  have hl := (hz2.mul ((Rd.opU l L ι W (P + Q)).mul (Rd.opU l L ι W (P - Q)))).2
  have hr := (((Rd.const l ι W (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    (((Rd.const l ι W (L.weierstrassP Q)).mul hz2).add
      ((Rd.const l ι W (-1)).mul ((Rd.const l ι W 1).add (hz2.mul hex))))).mul
    ((Rd.opU l L ι W P).mul (Rd.opU l L ι W P))).2
  have key := hl.symm.trans ((inW_congr l ι W hev).trans hr)
  simp only [map_pow, map_neg, map_one] at key
  have hw := wpInW hU
  rw [cc_gW, px_ptW hU Q hQ, scaled_x_model_point_lattice l L ι W P hP]
  unfold gW
  simp only [map_pow, xc, map_sub]
  apply mul_left_cancel₀ (pow_ne_zero 2 (lg_ne l W))
  linear_combination (X ^ 2 * B.fExp (phW l L ι W) ^ 2) * key -
    (C (ι (F.opU L Q (F.sgStar L) 0)) ^ 2 * B.fExp (phW l L ι W) ^ 2 *
      inW l ι W (F.opU L P (F.sgStar L)) ^ 2) * hw

theorem ptW_add_lattice (hU : Unif l L ι W) (t ω : ℂ) (hω : ω ∈ L.lattice) :
    ptW l L ι W (t + ω) = ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have h' : t + ω ∈ L.lattice := add_mem ht hω
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ h', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
  · have h' : t + ω ∉ L.lattice := fun h => ht (by simpa using sub_mem h hω)
    have e1 : L.weierstrassP (t + ω) = L.weierstrassP t := by
      first
      | exact L.weierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.weierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.weierstrassP_add_coe t ⟨ω, hω⟩
    have e2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := by
      first
      | exact L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.derivWeierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
    rw [ptW_notMem hU _ h', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨by simp only [xc, e1], by simp only [yc, e1, e2]⟩

theorem ptW_neg (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W (-t) = -ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have ht' : -t ∈ L.lattice := neg_mem ht
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
    first | simp | rfl | exact neg_zero.symm
  · have ht' : -t ∉ L.lattice := fun h => ht (by simpa using neg_mem h)
    rw [ptW_notMem hU _ ht', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    first
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg] <;> ring)
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, L.weierstrassP_neg, L.derivWeierstrassP_neg] <;> ring)

section Law

variable [DecidableEq ℂ_[l]]

theorem ptW_add_generic (hU : Unif l L ι W) (s t : ℂ) (hs : s ∉ L.lattice) (ht : t ∉ L.lattice)
    (hp : s + t ∉ L.lattice) (hm : s - t ∉ L.lattice) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  have hne := AddThm.P_sub_ne L s t hs ht hp hm
  have hne' : ι (L.weierstrassP s) - ι (L.weierstrassP t) ≠ 0 := by
    rw [← map_sub]
    exact fun h => hne (ι.injective (h.trans (map_zero ι).symm))
  have hd : xc l L ι W s - xc l L ι W t = ι (L.weierstrassP s) - ι (L.weierstrassP t) := by
    simp only [xc]
    ring
  have hx : xc l L ι W s ≠ xc l L ι W t := sub_ne_zero.1 (by rw [hd]; exact hne')
  have hX := congrArg ι (AddThm.P_add L s t hs ht hp hm)
  have hY := congrArg ι (AddThm.collinear L s t hs ht hp)
  simp only [map_pow, map_sub, map_mul, map_add, map_neg, map_div₀, map_ofNat] at hX hY
  rw [ptW_notMem hU s hs, ptW_notMem hU t ht, ptW_notMem hU _ hp,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have e1 : xc l L ι W (s + t) =
      W.toAffine.addX (xc l L ι W s) (xc l L ι W t)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.addX, xc, yc, WeierstrassCurve.b₂]
    rw [hX]
    field_simp
    ring
  have e2 : yc l L ι W (s + t) =
      W.toAffine.addY (xc l L ι W s) (xc l L ι W t) (yc l L ι W s)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← e1,
      WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.negY, xc, yc]
    field_simp
    linear_combination 144 * hY
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨e1, e2⟩

theorem ptW_add (hU : Unif l L ι W) (s t : ℂ) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  by_cases hs : s ∈ L.lattice
  · rw [add_comm s t, ptW_add_lattice hU t s hs, ptW_mem l L ι W s hs, zero_add]
  by_cases ht : t ∈ L.lattice
  · rw [ptW_add_lattice hU s t ht, ptW_mem l L ι W t ht, add_zero]
  by_cases hp : s + t ∈ L.lattice
  · have h : ptW l L ι W t = -ptW l L ι W s := by
      rw [← ptW_neg hU, ← ptW_add_lattice hU (-s) (s + t) hp]
      congr 1
      ring
    rw [ptW_mem l L ι W _ hp, h, add_neg_cancel]
  by_cases hm : s - t ∈ L.lattice
  · have h1 : ptW l L ι W s = ptW l L ι W t := by
      rw [← ptW_add_lattice hU t (s - t) hm]
      congr 1
      ring
    have h2 : ptW l L ι W (s + t) = ptW l L ι W (t + t) := by
      rw [← ptW_add_lattice hU (t + t) (s - t) hm]
      congr 1
      ring
    have htt : t + t ∉ L.lattice := fun h => hp (by
      have := L.lattice.add_mem h hm
      convert this using 1
      ring)
    obtain ⟨u, hu2, hup, hum⟩ := AddThm.exists_finite_part_one_idele_split_congruence_quotient L t
    have hu : u ∉ L.lattice := fun h => hu2 (by
      rw [two_mul]
      exact L.lattice.add_mem h h)
    have hu' : -u ∉ L.lattice := fun h => hu (by simpa using L.lattice.neg_mem h)
    have a1 : ptW l L ι W ((t + u) + (t - u)) = ptW l L ι W (t + u) + ptW l L ι W (t - u) :=
      ptW_add_generic hU _ _ hup hum (by convert htt using 2; ring) (by convert hu2 using 2; ring)
    have a2 : ptW l L ι W (t + u) = ptW l L ι W t + ptW l L ι W u :=
      ptW_add_generic hU _ _ ht hu hup hum
    have a3 : ptW l L ι W (t + -u) = ptW l L ι W t + ptW l L ι W (-u) :=
      ptW_add_generic hU _ _ ht hu' (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])
    rw [h2, h1]
    have e : t + t = (t + u) + (t - u) := by ring
    rw [e, a1, a2, sub_eq_add_neg, a3, ptW_neg hU]
    abel
  exact ptW_add_generic hU s t hs ht hp hm

end Law

end AnaSysW

theorem analytic_point_eq_zero_iff : PtWZero := by
  intro l _ L ι W hU t
  exact AnaSysW.ptW_zero_iff hU t

open Classical in

theorem analytic_point_map_add : PtWAdd := by
  intro l _ L ι W hU s t
  exact AnaSysW.ptW_add hU s t

theorem weierstrass_series_eq_transported (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (W : WeierstrassCurve ℂ_[l]) (hU : Unif l L ι W) :
    Formalism.L2.Th1.A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L) := by
  exact AnaSysW.wpBridge hU

open Classical in

theorem analytic_translate_system_model : AnalyticSysW := by
  unfold AnalyticSysW
  intro l _ L ι W hU π hπ
  unfold IsTransSys
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [hπ] at ht
    exact AnaSysW.gW_mem (l := l) (L := L) (ι := ι) (W := W) t ((AnaSysW.ptW_zero_iff hU t).1 ht)
  · intro t ht
    simp only [hπ] at ht
    have htl : t ∉ L.lattice := fun h => ht ((AnaSysW.ptW_zero_iff hU t).2 h)
    rw [AnaSysW.cc_gW (l := l) (L := L) (ι := ι) (W := W) t]
    refine (map_ne_zero ι).mpr ?_
    simp only [F.opU, F.sgStar, zero_add]
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
    exact fun h => htl ((F.sigmaZero L t).1 h)
  · intro P Q hQ
    simp only [hπ] at hQ ⊢
    have hQl : Q ∉ L.lattice := fun h => hQ ((AnaSysW.ptW_zero_iff hU Q).2 h)
    by_cases hP : P ∈ L.lattice
    · exact AnaSysW.prod_mem hU P Q hQl hP
    · exact AnaSysW.prod_notMem hU P Q hQl hP

end Formalism.L2.Th1.E
