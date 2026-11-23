import Development.WeilBound.CoreStatements.CentralCharts.IsCoeffAtOfSmul
import Development.WeilBound.CoreStatements.CentralCharts.ChartAnalytic
import Development.WeilBound.CoreStatements.CentralCharts.OneLeDimFl
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdegStatement

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology

theorem sum_Iic_tele {N : ℕ} (g : ℕ → ℝ) (i : Fin N) :
    ∑ k ∈ Finset.Iic i, (g ((k : ℕ) + 1) - g k) = g ((i : ℕ) + 1) - g 0 := by
  rw [← Finset.sum_range_sub g]
  refine Finset.sum_bij (fun k _ => (k : ℕ)) (fun k hk => ?_) (fun a _ b _ h => Fin.ext h) (fun m hm => ?_)
    fun _ _ => rfl
  · have : k ≤ i := Finset.mem_Iic.1 hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le this)
  · have h := Finset.mem_range.1 hm
    exact ⟨⟨m, by omega⟩, Finset.mem_Iic.2 (show m ≤ (i : ℕ) by omega), rfl⟩

theorem sum_Ioi_tele {N : ℕ} (g : ℕ → ℝ) (i : Fin N) :
    ∑ k ∈ Finset.Ioi i, (g ((k : ℕ) + 1) - g k) = g N - g ((i : ℕ) + 1) := by
  have h1 : ∑ k : Fin N, (g ((k : ℕ) + 1) - g k) = g N - g 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) N, Finset.sum_range_sub g]
  have h2 := Finset.sum_add_sum_compl (Finset.Iic i) fun k : Fin N => g ((k : ℕ) + 1) - g k
  rw [sum_Iic_tele, h1, show (Finset.Iic i)ᶜ = Finset.Ioi i by ext; simp] at h2
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l} [NumberField c.F]
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] [CharZero Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem central_chart (h0 : Flat.FlatLineGenerator) (h1 : Flat.FlatLineGeneratorComponent) (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (ha : χ.a = 0) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) :
    ∃ (F : (Fin n → ℂ) → ℂ) (d : ℝ), AnalyticAt ℂ F 0 ∧ F 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∑ i, Real.log ((hx (τ, i)).h (χ.γ t)) = Real.log ‖F t‖ + d := by
  have pts : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  obtain ⟨z₀, hz₀⟩ := pts _ (χ.mem 0 (Metric.mem_ball_self one_pos))
  obtain ⟨c₁, a, tt, h⟩ := central h0 h1 hS hpq 𝔐 Fl xdeg e hx hroot hhod hdg τ
  choose cc hcc0 using hz₀.1
  have hc0 : ∀ k, χ.γ 0 ⟨k, cc k⟩ ≠ 0 := fun k => (hcc0 k).ne_zero
  have hcc : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k, χ.γ t ⟨k, cc k⟩ ≠ 0 :=
    eventually_all.2 fun k => (chart_analytic χ _).continuousAt.eventually_ne (hc0 k)
  obtain ⟨⟨v, hv0, hv⟩, -⟩ := h z₀ _ hz₀ cc hc0
  obtain ⟨F₁, hF₁, hF0, hF⟩ := exists_val_fam 𝔐.tie 𝔐.all (chart_analytic χ) hz₀ hv
  obtain ⟨s, hs⟩ := exists_emb_fam 𝔐 (chart_analytic χ) hz₀
  refine ⟨fun t => F₁ t * ∏ k, χ.γ t ⟨k, cc k⟩ ^ a k, -tt s, hF₁.fun_mul
    (Finset.analyticAt_fun_prod _ fun k _ => (chart_analytic χ _).fun_zpow (hc0 k)),
    mul_ne_zero (by rw [hF0]; exact hv0) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc0 k)), ?_⟩
  filter_upwards [hF, hcc, hs, Metric.ball_mem_nhds (0 : Fin n → ℂ) one_pos] with t h2 h3 h5 h4
  obtain ⟨z, hz⟩ := pts _ (χ.mem t h4)
  have hi : 𝔐.Interior z := by_contra fun hn => by
    obtain ⟨i, hi, -⟩ := (χ.boundary t h4).1 ((hBd z _ hz).2 hn)
    omega
  have e1 := (h z _ hz cc h3).2 hi s (h5 z hz) _ (h2 z hz)
  have p3 : ∀ i, 0 < (hx (τ, i)).h (χ.γ t) := fun i => (hx _).pos _ fun k => ⟨cc k, h3 k⟩
  simp only [norm_mul, norm_prod, norm_zpow]
  rw [e1, Real.log_mul (Real.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun i _ => (p3 i).ne'), Real.log_exp,
    Real.log_prod fun i _ => (p3 i).ne']
  ring

theorem local_bounds (hG : Top.Given) (h0 : Flat.FlatLineGenerator) (h1 : Flat.FlatLineGeneratorComponent) (hGl : Top.IsGlobal Xo l c Y)
    (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) (i : Fin (D.p + D.q)) :
    Tame χ.a (fun t => -∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t))) ∧
      (χ.a = 0 → PshAt0 (fun t => -∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t))) ∧
        ((i : ℕ) + 1 = D.p + D.q → PshAt0 fun t => ∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t)))) := by
  obtain ⟨M, F, hM0, hM, hF, hev⟩ := root_data hG hGl 𝔐 Fl hBd χ xdeg e hx hroot hhod hdg
  refine ⟨?_, fun ha => ?_⟩
  · have hr : ∀ r, Tame χ.a fun t => Real.log ((hx r).h (χ.γ t)) := fun r => by
      have t1 := (hM _ _ (HodgeCpt.rootIdx D r).2.2).1
      have t2 := (hM _ _ (HodgeCpt.rootIdx D r).2.2.le).1
      refine ((tame_log_norm χ.a (hF r).1 (hF r).2).add ((t1.add (t2.const_mul (-1))).const_mul
        (-((HodgeCpt.rootSgn D r : ℝ) / 2)))).congr ?_
      filter_upwards [hev r] with t ht hoff
      rw [ht hoff]
      simp only [Nat.succ_eq_add_one]
      ring
    refine ((Tame.sum (Finset.Iic i) fun k _ => hr (τ, k)).const_mul (-1)).congr ?_
    exact Eventually.of_forall fun t _ => by ring
  · have hall : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k : Fin (D.p + D.q), _ :=
      eventually_all.2 fun k => (hev (τ, k)).mono fun t ht => ht fun j hj => absurd hj (by omega)
    obtain ⟨Fc, d, hFc, hFc0, hc⟩ := central_chart h0 h1 hS hpq 𝔐 Fl hBd χ ha xdeg e hx hroot hhod hdg τ
    refine ⟨?_, fun hi => ?_⟩
    · by_cases hip : (i : ℕ) < D.p
      · refine ((PshAt0.sum (Finset.Iic i) fun k _ => pshAt0_log_norm (-1) 0 (hF (τ, k)).1 (hF (τ, k)).2).add
          (((hM (.inl τ) ((i : ℕ) + 1) hip).2 ha).const_mul (c := 1 / 2) (by norm_num))).congr ?_
        filter_upwards [hall] with t ht
        have e1 : ∀ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ -
            1 / 2 * (M (.inl τ) ((k : ℕ) + 1) t - M (.inl τ) k t) := fun k hk => by
          have hk' : (k : ℕ) < D.p := lt_of_le_of_lt (Fin.le_def.1 (Finset.mem_Iic.1 hk)) hip
          have e2 : HodgeCpt.rootIdx D (τ, k) = ⟨.inl τ, ⟨k, hk'⟩⟩ := dif_pos hk'
          have e3 : HodgeCpt.rootSgn D (τ, k) = 1 := if_pos hk'
          have := ht k
          rw [e2, e3] at this
          simpa using this
        rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum,
          sum_Iic_tele (fun m => M (.inl τ) m t), hM0]
        simp only [neg_mul, _root_.one_mul, add_zero, Finset.sum_neg_distrib]
        ring
      · refine (((PshAt0.sum (Finset.Ioi i) fun k _ => pshAt0_log_norm 1 0 (hF (τ, k)).1 (hF (τ, k)).2).add
          (((hM (.inr τ) (D.p + D.q - ((i : ℕ) + 1)) (by show _ ≤ D.q; omega)).2 ha).const_mul (c := 1 / 2)
            (by norm_num))).add (pshAt0_log_norm (-1) (-d) hFc hFc0)).congr ?_
        filter_upwards [hall, hc] with t ht hct
        have e1 : ∀ k ∈ Finset.Ioi i, Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ -
            1 / 2 * (M (.inr τ) (D.p + D.q - ((k : ℕ) + 1)) t - M (.inr τ) (D.p + D.q - k) t) := fun k hk => by
          have hk0 : (i : ℕ) < k := Fin.lt_def.1 (Finset.mem_Ioi.1 hk)
          have hk' : ¬ (k : ℕ) < D.p := by omega
          have hk2 := k.2
          have e2 : HodgeCpt.rootIdx D (τ, k) = ⟨.inr τ, ⟨D.p + D.q - 1 - k, by show _ < D.q; omega⟩⟩ := dif_neg hk'
          have e3 : HodgeCpt.rootSgn D (τ, k) = -1 := if_neg hk'
          have := ht k
          rw [e2, e3] at this
          have h2 : Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ - ((-1 : ℤ) : ℝ) / 2 *
              (M (.inr τ) (D.p + D.q - 1 - k + 1) t - M (.inr τ) (D.p + D.q - 1 - k) t) := this
          rw [show D.p + D.q - 1 - k + 1 = D.p + D.q - k by omega,
            show D.p + D.q - 1 - k = D.p + D.q - (k + 1) by omega] at h2
          rw [h2]
          push_cast
          ring
        have e4 := Finset.sum_add_sum_compl (Finset.Iic i) fun k => Real.log ((hx (τ, k)).h (χ.γ t))
        rw [show (Finset.Iic i)ᶜ = Finset.Ioi i by ext; simp, Finset.sum_congr rfl e1, Finset.sum_sub_distrib,
          ← Finset.mul_sum, sum_Ioi_tele (fun m => M (.inr τ) (D.p + D.q - m) t), Nat.sub_self, hM0, hct] at e4
        simp only [_root_.one_mul, add_zero]
        linarith
    · refine (pshAt0_log_norm 1 d hFc hFc0).congr ?_
      filter_upwards [hc] with t hct
      rw [show Finset.Iic i = Finset.univ by
        ext k
        have := k.2
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
        omega, hct, _root_.one_mul]

end AnalyticReference.An

namespace AnalyticReference

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem reference_geometry_holomorphic_inverse : Top.Given → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∀ G : RefGeo Y, ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) := by
  intro hG h0 h1 E _ _ _ H D Xo l c Y hGl hS hp hq G
  haveI := c.fin
  haveI : NumberField c.F := {}
  choose sing hdeg hhod hconj using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l (Xo l) c _ _ Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl G.xdeg G.e
    RingOfIntegers.coe_injective G.lines
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  exact An.of_local hI hp hq G sing hdeg hhod hconj fun χ τ i =>
    An.local_bounds hG h0 h1 hGl hS (by omega) G.𝔐 G.Fl G.bd_iff χ G.xdeg G.e sing G.lines hhod hdeg τ i

end AnalyticReference
