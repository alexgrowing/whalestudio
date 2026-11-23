import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GaugeBaseChange

open GlobalTheory.QuadDeriv

section

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}

theorem map_ev_two {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mapP φ a, mapP φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem baseChange_zero₂ {n : ℕ} : mapP φ (0 : Pt k n d) = 0 := funext fun _ => map_zero _

theorem map_expS [Algebra ℚ k] [Algebra ℚ k'] {n : ℕ} (f : PS k n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS k f) = FB.expS k' (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_dpolyOf (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f : PS k 1 d) :
    MvPowerSeries.map φ (DpolyOf F u P f) =
      DpolyOf (mapP φ F) (fun l i => φ (u l i)) (MvPolynomial.map φ P) (MvPowerSeries.map φ f) := by
  rw [GE.dpolyOf_eq_sum_of_subset _ _ (MvPolynomial.map φ P) P.support
    (MvPolynomial.support_map_subset _ _), DpolyOf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_C, GlobalTheory.map_dmonOf, MvPolynomial.coeff_map]
  rfl

end

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
  {k k' : Type} [CommRing k] [Algebra R k] [CommRing k'] [Algebra R k'] (β : k →ₐ[R] k')

theorem map_map_alg {σ : Type} (f : MvPowerSeries σ R) :
    MvPowerSeries.map (β : k →+* k') (MvPowerSeries.map (algebraMap R k) f) =
      MvPowerSeries.map (algebraMap R k') f := by
  ext m
  simp [coeff_map]

theorem mapP_FK : mapP (β : k →+* k') (B.FK k) = B.FK k' :=
  funext fun i => map_map_alg β (B.G.F i)

theorem baseChange_actK (a : O) : mapP (β : k →+* k') (B.actK k a) = B.actK k' a :=
  funext fun i => map_map_alg β (B.A.act a i)

theorem gp_FK : GP (B.FK k) := constantCoeff_mapP_eq_zero (algebraMap R k) _ B.G.const

theorem gp_actK (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero (algebraMap R k) _ (B.A.const a)

theorem const_of_axis {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) : constantCoeff h = 0 := by
  have := gt_const_ev_eq (n := 1) ![0, pt k d 0] (pair_points_zero_constant gp_zero₂ (gp_pt 0)) h
  rw [← this, h0, map_zero]

variable [Algebra ℚ k] [Algebra ℚ k']

theorem isCanonGauge_map {h : PS k 2 d} (H : B.IsCanonGauge k h) :
    B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) := by
  have hc := const_of_axis H.ax0
  have c2 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] h) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) h hc
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ (gp_FK B) _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (gp_actK B a) (gp_pt i)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax0
    rwa [map_ev_two _ _ _ gp_zero₂ (gp_pt 0), baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax1
    rwa [map_ev_two _ _ _ (gp_pt 0) gp_zero₂, baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph1
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add, c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gA _ _) (gp_pt _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gA _ _) (gp_pt _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph2
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add, c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gp_pt _) (gA _ _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gp_pt _) (gA _ _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.sy
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gp_pt _) (gp_pt _), hc, sub_zero]), map_sub,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _)] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) (H.ad a)
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gC _ _) (gp_pt _), c2 _ _ (gp_pt _) (gC _ _), sub_zero]), map_sub,
      map_ev_two _ _ _ (gC _ _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gC _ _),
      baseChange_comp1 _ _ _ (gp_pt _), baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_actK] at this
    simpa only [baseChange_pt] using this

theorem nabVal_map {h : PS k 2 d} (hc : constantCoeff h = 0) (w0 : O) (m : ℕ) (f : PS k 1 d) {Λ : Type}
    [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) :
    B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f)
      (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  have gC : GP (comp1 (B.actK k w0) (pt k (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL k h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (β : k →+* k') (B.hL k h w0) =
      B.hL k' (MvPowerSeries.map (β : k →+* k') h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_pt]
  unfold FB.nabVal
  change _ = (β : k →+* k') _
  rw [← MvPowerSeries.constantCoeff_map, map_dpolyOf, mapP_FK, map_mul,
    map_expS _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, cL, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast (β : k →+* k'), eL]
  rfl

end GlobalTheory.GaugeBaseChange

namespace GlobalTheory

theorem canonGauge_nabVal_baseChange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k k' : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing k'] [Algebra ℚ k'] [Algebra R k'] (β : k →ₐ[R] k') (h : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) ∧ ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k), B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f) (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  intro R _ d O _ _ B k k' _ _ _ _ _ _ β h H
  exact ⟨GaugeBaseChange.isCanonGauge_map B β H, fun w0 m f _ _ u Q =>
    GaugeBaseChange.nabVal_map B β (GaugeBaseChange.const_of_axis H.ax0) w0 m f u Q⟩

end GlobalTheory
