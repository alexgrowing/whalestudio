import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.CentreIdent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {n a : ℕ}

theorem abPart_principal (C : Flat.BdryChart Xo σ₀ n a) {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (P : AbPart C.t (spMap (C.ψ z))) : IsPrincipal P.tB := by
  obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := GlobalTheory.T.exists_dvr_through_disc_point E H D l Xo σ₀ n a C z hz
  have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
    rintro _ rfl P
    obtain ⟨m', -⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ tV C.t _ mV ℂ (spMap r) P
    exact GlobalTheory.T.polarized_abelian_part_principal E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  refine key _ ?_ P
  rw [← hrf]
  show Spec.map (CommRingCat.ofHom (r.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_seq_cover (h : a ≤ n) : ∃ ws : ℕ → Fin n → ℂ, (∀ k, ws k ∈ logCover h) ∧
    Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) := by
  refine ⟨fun m i => if (i : ℕ) < a then -((m : ℂ) + 1) else 0, fun m => ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
  · have hi : ((Fin.castLE h i : Fin n) : ℕ) < a := by simp
    simp only [hi, ↓reduceIte, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have hi' : ¬ ((i : ℕ) < a) := by omega
    simp [hi']
  · rw [tendsto_pi_nhds]
    intro i
    by_cases hi : (i : ℕ) < a
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      exact tendsto_const_nhds

theorem periods_inj {g : ℕ} {Λ : Type} [AddCommGroup Λ] (L₀ : Flat.LogPeriods n a g Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L₀.a_le) : Function.Injective (L₀.P w) := by
  intro x x' hxx
  have h0 : L₀.P w (x - x') = 0 := by rw [map_sub, hxx, sub_self]
  have hE : L₀.E (x - x') = 0 := by
    refine LinearMap.ext fun y => ?_
    have him := L₀.im w hw (x - x') y
    rw [h0] at him
    have h2 : ((L₀.E (x - x') y : ℤ) : ℝ) = 0 := by
      rw [← him]
      simp
    rw [LinearMap.zero_apply]
    exact_mod_cast h2
  exact sub_eq_zero.1 (L₀.unimod.1 (hE.trans (map_zero L₀.E).symm))

theorem centre_phi (C : Flat.BdryChart Xo σ₀ n a) {X : Scheme.{0}} {tt : SAB H X} {jj : Sp C.R ⟶ X}
    (m : SABMap C.t tt jj) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ)
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (L : ActPeriods E n a C.g Λ)
    (hlink : ∀ w ∈ logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • expCover a w) ↔ ∃ x, L.P w x = p) ∧
      ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → CubWeil C.t.cub N (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x))
        (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.toLogPeriods.E x x' : ℤ) : ℂ) / N))
    (hB : ∀ c x, e.ex ((ρ : ℂ) • 0) (L.B 0 c x) = e.ex ((ρ : ℂ) • 0) x ≫ C.t.act.act c)
    {A : Type} [Fintype A] {k : ℕ} (σ : A → (𝓞 E →+* ℂ)) (b : A → Fin k → (Fin n → ℂ) → Fin C.g → ℂ)
    (sc : A → Fin k → Fin C.g → C.R) (hb0 : ∀ τ i, b τ i 0 = fun j => C.ψ ((ρ : ℂ) • 0) (sc τ i j))
    (hσ : IsCMFam σ) (hb : IsEigFrames (Metric.ball 0 1) L.B σ b)
    (P : AbPart tt (spMap (C.ψ ((ρ : ℂ) • 0)) ≫ jj))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρV : 𝓞 E →+* Module.End ℂ V) (I₀ : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρV)
    (hI₀ : P.IsCochars MV I₀)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (bz : A → Fin k → V) (hbz : ∀ τ i, (MV.pt (bz τ i)).left ≫ P.m.φ =
      spMap (dualMap (C.ψ ((ρ : ℂ) • 0))) ≫ (C.M.pt (sc τ i)).left ≫ m.φ)
    {ν : ℝ} (hν : PhiNormSq ρV hf I₀ (4 * Real.pi)⁻¹ σ bz ν) :
    ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) := by
  obtain ⟨W, I, per, s, Hb, hI, hsat, -, hs, hlim, -, hH, hIm, hrad, hlimν⟩ := GlobalTheory.T.period_decomposition_near_boundary E n a C.g Λ A L σ k b hσ hb
  have h00 : (ρ : ℂ) • (0 : Fin n → ℂ) = 0 := smul_zero _
  have hbρ : (ρ : ℂ) • (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    rw [h00]; exact Metric.mem_ball_self hρ0
  have hol : Flat.IsHolPts (Metric.ball 0 ρ) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  obtain ⟨ws, hws, hw0⟩ := exists_seq_cover L.a_le
  have hper : ∀ x : W, Tendsto (fun j => L.P (ws j) x) atTop (𝓝 (per x)) := fun x => by
    obtain ⟨h1, h2, h3⟩ := hs x
    have := h1.tendsto.comp hw0
    rw [h2] at this
    exact this.congr fun j => h3 _ (hws j)
  have hfour : ∀ (x : ℕ → Λ) (p : Fin C.g → ℂ), Tendsto (fun j => L.P (ws j) (x j)) atTop (𝓝 p) →
      ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ j in atTop, x j = x₀ := by
    intro x p hx
    obtain ⟨x₀, rfl⟩ := hlim ws x p hws hw0 hx
    refine ⟨x₀, rfl, ?_⟩
    have h1 : Tendsto (fun j => ((ρ : ℂ) • expCover a (ws j), L.P (ws j) (x j - x₀))) atTop (𝓝 ((ρ : ℂ) • 0, 0)) := by
      refine (hw0.const_smul _).prodMk_nhds ?_
      have := hx.sub (hper x₀)
      rw [sub_self] at this
      simpa only [map_sub] using this
    filter_upwards [h1.eventually (per_small e hbρ (Metric.isOpen_ball.mem_nhds hbρ))] with j hj
    have h2 := hj (((hlink _ (hws j)).1 _).2 ⟨_, rfl⟩)
    exact sub_eq_zero.1 (periods_inj L.toLogPeriods (hws j) (h2.trans (map_zero _).symm))
  obtain ⟨hA, hBp, hC⟩ := GlobalTheory.T.family_exp_log_cover_bound E H C.R C.t C.g n a C.M C.ψ ρ e Λ L.toLogPeriods hρ0 hρ1 hol hlink 0
    (Metric.mem_ball_self one_pos) ws (W.restrictScalars ℤ) per hws hw0 hper hfour
  replace hA : ∀ x : W, per x ∈ e.per ((ρ : ℂ) • 0) := hA
  replace hBp : ∀ p ∈ e.per ((ρ : ℂ) • 0), ∃ x : W, per x = p := hBp
  obtain ⟨m', hm'⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ C.t tt jj m ℂ _ P
  let P' : AbPart C.t (spMap (C.ψ ((ρ : ℂ) • 0))) := ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  have hP := abPart_principal C (Metric.ball_subset_ball hρ1 hbρ) P'
  obtain ⟨Mz, hMz⟩ := GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo σ₀ n a C ((ρ : ℂ) • 0)
  have hL : ∀ i, C.M.Lifts (C.ψ ((ρ : ℂ) • 0)) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1)) := fun i => by
    have h1 := hMz (Pi.single i 1)
    have h2 : (fun j => C.ψ ((ρ : ℂ) • 0) ((Pi.single i 1 : Fin C.g → C.R) j)) = (Pi.single i 1 : Fin C.g → ℂ) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rwa [h2] at h1
  obtain ⟨Φ, f1, f2, f3, f4⟩ := centre_ident e hbρ P' hP Mz hL MV ρV I₀ hf hact hI₀ hh (L.B 0) hB Hb hH
    (fun y hy y' hy' => by
      obtain ⟨x, rfl⟩ := hBp y hy
      obtain ⟨x', rfl⟩ := hBp y' hy'
      exact ⟨_, hIm x x', fun N ζ hN hζ => hC N ζ x x' hN hζ⟩)
    {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}
    (fun p => ⟨by
      rintro ⟨x, hx, rfl⟩
      refine ⟨hA x, fun y hy => ?_⟩
      obtain ⟨x', rfl⟩ := hBp y hy
      rw [hIm x x', ((hI _).1 hx).2 _ x'.2, Int.cast_zero], by
      rintro ⟨hp, h0⟩
      obtain ⟨x, rfl⟩ := hBp p hp
      refine ⟨x, (hI _).2 ⟨x.2, fun y hy => ?_⟩, rfl⟩
      have := h0 _ (hA ⟨y, hy⟩)
      rw [hIm x ⟨y, hy⟩] at this
      exact_mod_cast this⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hrad x hx)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Ψ : V ≃ₗ[ℂ] (Fin C.g → ℂ) := Φ.trans (LinearEquiv.smulOfNeZero ℂ _ _ hc)
  have hΨ : ∀ x, Ψ x = (2 * Real.pi * Complex.I : ℂ) • Φ x := fun x => rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨ν', hν', hνe⟩ := phi_transport ρV (L.B 0) Ψ (fun c x => by rw [hΨ, hΨ, map_smul, f2]) hf
    (fun x y => y ⬝ᵥ Hb *ᵥ star x) (4 * Real.pi)⁻¹
    (fun x x' => by
      rw [f3, hΨ, hΨ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      push_cast
      field_simp
      linear_combination (4 * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) * Complex.I_mul_I)
    I₀ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x})
    (by
      rw [← AddSubgroup.closure_eq (I₀.map Ψ.toLinearMap.toAddMonoidHom)]
      congr 1
      ext p
      rw [f4]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩)
    σ bz (fun τ i => b τ i 0) _ hc
    (fun τ i => by
      rw [hΨ, hb0]
      congr 1
      refine Mz.inj (Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_))
      · have h1 := hMz (sc τ i)
        unfold LieModel.Lifts at h1
        rw [Category.comp_id] at h1
        rw [f1, h1, Category.assoc, Category.assoc]
        exact (congrArg _ hm').trans (hbz τ i)
      · rw [Over.w (Mz.pt _), Over.w (Mz.pt _)])
    ν hν
  obtain ⟨hpos, hlim'⟩ := hlimν ν' hν'
  have e1 : (4 * Real.pi)⁻¹ * ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 = Real.pi := by
    have := Real.pi_pos
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg this.le]
    field_simp
    ring
  have e2 : Real.log ν = (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) + Real.log ν' := by
    rw [hνe, e1, Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
    push_cast
    ring
  refine ⟨I, hsat, fun v hv w hw => ((hI _).1 hv).2 _ ((hI _).1 hw).1, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hlim' ε hε
  refine ⟨δ, hδ, fun w hw h1 => ?_⟩
  have := (abs_lt.1 (h w hw h1)).1
  linarith

end LevelTowerAlt.Val
