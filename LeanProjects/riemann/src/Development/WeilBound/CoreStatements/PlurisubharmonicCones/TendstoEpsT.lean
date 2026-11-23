import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPshPull
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvCEqZeroIffOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement

open Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.Build
open MvPolynomial (rename)

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem psh_mono {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P Θ : LocPot X} (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) {c c' : ℝ} (hc : c ≤ c') (h : IsPsh A (P + Θ.rsmul c)) :
    IsPsh A (P + Θ.rsmul c') := by
  have h7 := isPshAdd A _ _ (isPotentialAdd _ _ _ hP (pot_rsmul hΘ c)) (pot_rsmul hΘ (c' - c)) h
    (isPshRsmul A _ _ (sub_nonneg.2 hc) hΘ (TailBoundAlt.isPsh_of_isPosPot _ _ hΘp))
  refine TailBoundAlt.isPsh_congr A _ _ h7 (fun x y hy => ⟨hy, hy.2⟩) ?_
  funext x y
  show _ + _ * Θ.φ x y = P.φ x y + c * Θ.φ x y + _ * Θ.φ x y
  show P.φ x y + _ = _
  ring

theorem tendsto_epsT (C : ℝ) : Tendsto (epsT C) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    simp only [one_div]
    exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h2 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp h1).const_mul C
  rw [mul_zero] at h2
  exact h2.congr fun t => by simp [epsT, mul_div_assoc]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_comb {σ : Type} [Fintype σ] (A : σ → HermLine J) (n : σ → ℤ) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine A n).h z) = ∑ a, (n a : ℝ) * Real.log ((A a).h z) := by
  simp only [Top.combLine]
  rw [Real.log_prod fun a _ => (zpow_pos ((A a).pos z hz) _).ne']
  simp only [Real.log_zpow]

theorem den_ne {P : Ideal (MRing J)} (hP : P.IsPrime) {f g u v : MRing J} (h : UnitRatio P f g) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts P) (huv : u * f - v * g ∈ P) (hu : evC z u ≠ 0) : evC z v ≠ 0 := by
  obtain ⟨u', v', h1, -, h2⟩ := OneModel.exists_pair_ne h hz
  have h3 : (u * v' - u' * v) * g ∈ P := by
    have := P.sub_mem (P.mul_mem_left u' huv) (P.mul_mem_left u h1)
    convert this using 1
    ring
  have h4 : evC z (u * v' - u' * v) = 0 := hz.2 _ ((hP.mem_or_mem h3).resolve_right h.2.1)
  intro h0
  have h5 : evC z (u * v' - u' * v) = evC z u * evC z v' - evC z u' * evC z v := by simp [evC]
  rw [h5, h0, mul_zero, sub_zero] at h4
  exact mul_ne_zero hu h2 h4

theorem log_defect {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (‖a‖ / ‖b‖ * x / y) = Real.log (‖a‖ / ‖b‖) + Real.log x - Real.log y := by
  have : 0 < ‖a‖ / ‖b‖ := div_pos (norm_pos_iff.2 ha) (norm_pos_iff.2 hb)
  rw [Real.log_div (mul_pos this hx).ne' hy.ne', Real.log_mul this.ne' hx.ne']

theorem abs_sum_le {σ : Type} [Fintype σ] (m : σ → ℤ) {u : σ → ℝ} {c : ℝ} (h : ∀ a, |u a| ≤ c) :
    |∑ a, (m a : ℝ) * u a| ≤ (∑ a, |(m a : ℝ)|) * c := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h a) (abs_nonneg _)

theorem anCore (hR : Replace) (hB : BaseSide) (hI : PB.Inputs) (hK : ResK.ResKStatement) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) {K₁ : Type} [Fintype K₁] {J₁ : K₁ → Type} [∀ k, Fintype (J₁ k)] {P₁ : Ideal (MRing J₁)}
    {d : ℕ} {σ : Type} [Fintype σ] [Nonempty σ] {S : PB.AnSys d σ} (Re : PB.Realis S P₁) (alg : AlgOver Re) (m : σ → ℤ)
    (Sg : HermLine J₁) (hSa : Sg.a = (Top.combLine Re.ref m).a)
    (hSh : ∀ x, Re.π x ∉ bdry S.s → Real.log (Sg.h (Re.R.lift x x)) =
      ∑ a, (m a : ℝ) * (Real.log ((Re.ref a).h (Re.R.lift x x)) + S.ph a (Re.π x)))
    {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    {D : ComponentData II Ψ K J Ω W} (Hd : HodgeData D) {M : XModel D} (Sr : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ)
    (hSr : Sr.IsTied) {K₃ : Type} [Fintype K₃] {ρ : K₃ → Type} [∀ k, Fintype (ρ k)] {κ₁ : K₁ → K₃}
    {v₁ : (Σ k, J₁ k) → Σ k, ρ k} {κ₂ : K → K₃} {v₂ : (Σ k, J k) → Σ k, ρ k} {Ω₃ : Type} [Field Ω₃] [CharZero Ω₃]
    {y : (Σ k, ρ k) → Ω₃} {β : MRing ρ} {b : K₃ → ℕ} (hb₁ : IsBlockMap κ₁ v₁) (hb₂ : IsBlockMap κ₂ v₂)
    (he₁ : mCoordIdeal (y ∘ v₁) = P₁) (he₂ : mCoordIdeal (y ∘ v₂) = mCoordIdeal D.y) (har : IsArithVar (mCoordIdeal y) (d + 1))
    (hβ : IsMultiHomog β b) (hβn : β ∉ mCoordIdeal y)
    (hbd₂ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β ≠ 0 → (fun p => z (v₂ p)) ∉ D.Bd)
    (hiso : ∀ L L' : HermLine ρ, IsPullHerm κ₁ v₁ Sg L → IsPullHerm κ₂ v₂ (muVert Hd B) L' →
      IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z β ≠ 0} L L') :
    ∃ (K' : Type) (_ : Fintype K') (ρ' : K' → Type) (_ : ∀ k, Fintype (ρ' k)) (κ : K₃ → K') (v : (Σ k, ρ k) → Σ k, ρ' k)
      (y' : (Σ k, ρ' k) → Ω₃), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧
      IsArithVar (mCoordIdeal y') (d + 1) ∧ ∀ (Mt : ℝ → HermLine ρ') (l : ℝ → σ → HermLine ρ'),
      (∀ t, IsPullHerm (κ ∘ κ₂) (v ∘ v₂) (muReg Hd Sr B t) (Mt t)) →
      (∀ t a, IsPullHerm (κ ∘ κ₁) (v ∘ v₁) (Re.line a t) (l t a)) → ∀ (a b : ℕ) (n : Fin b → Option σ → ℤ), a + b = d + 1 →
      Tendsto (fun t => II K' ρ' (mCoordIdeal y') (a + b) (Fin.append (fun _ : Fin a => Mt t)
          fun j => Top.combLine (fun o : Option σ => o.elim (SheetDecomposition.PF.cst ρ') (l t)) (n j)) -
        II K' ρ' (mCoordIdeal y') (a + b) (Fin.append
          (fun _ : Fin a => Top.combLine (fun o : Option σ => o.elim (SheetDecomposition.PF.cst ρ') (l t)) fun o => o.elim 0 m)
          fun j => Top.combLine (fun o : Option σ => o.elim (SheetDecomposition.PF.cst ρ') (l t)) (n j))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨γ, c, hγ, hγn, hz⟩ := exists_bdry_form Re alg
  have hjb := GlobalTheory.T.block_join_inclusions_compat
  have hn : rename v₁ γ ∉ mCoordIdeal y := fun h => hγn (by
    rw [← he₁, ← hjb.2.1 K₁ J₁ K₃ ρ κ₁ v₁ Ω₃ y hb₁]
    exact h)
  have hBn : β * rename v₁ γ ∉ mCoordIdeal y := fun h => (har.2.1.1.mem_or_mem h).elim hβn hn
  have hBh := Build.isMultiHomog_mul hβ (isMultiHomog_rename hb₁ hγ)
  obtain ⟨K', _, ρ', _, κ, v, y', J', R, Amp, hb, hy, hfield, har', -, -, hpot, hpos, hbad⟩ :=
    GlobalTheory.T.block_extension_arith_var hK K₃ ρ Ω₃ y d _ _ har hBh hBn
  refine ⟨K', inferInstance, ρ', inferInstance, κ, v, y', hb, hy, hfield, har', fun Mt l hMt hl a b n hab => ?_⟩
  have e₀ : imageZ v (mCoordIdeal y') = mCoordIdeal y := by rw [hjb.2.1 K₃ ρ K' ρ' κ v Ω₃ y' hb, hy]
  have hc₁ := hjb.2.2 K₁ J₁ K₃ ρ K' ρ' κ₁ v₁ κ v hb₁ hb
  have hc₂ := hjb.2.2 K J K₃ ρ K' ρ' κ₂ v₂ κ v hb₂ hb
  have e₁ : imageZ (v ∘ v₁) (mCoordIdeal y') = P₁ := by
    rw [hjb.2.1 K₁ J₁ K' ρ' (κ ∘ κ₁) (v ∘ v₁) Ω₃ y' hc₁.1, ← he₁, ← hy]
    rfl
  have e₂ : imageZ (v ∘ v₂) (mCoordIdeal y') = mCoordIdeal D.y := by
    rw [hjb.2.1 K J K' ρ' (κ ∘ κ₂) (v ∘ v₂) Ω₃ y' hc₂.1, ← he₂, ← hy]
    rfl
  obtain ⟨π, hπ, l₁, p₁, q₁⟩ := side hc₁.1 Re e₁ R har' alg
  have hB0 : ∀ z, evC z (rename v (β * rename v₁ γ)) = evC (fun p => z (v p)) β * evC z (rename (v ∘ v₁) γ) := by
    intro z
    rw [evC_rename, evC_mul, evC_rename (v ∘ v₁), evC_rename v₁]
    rfl
  have hbd₁ : ∀ x, π x ∈ bdry S.s → evC (R.lift x x) (rename v (β * rename v₁ γ)) = 0 := fun x hx => by
    rw [hB0, evC_bdry hc₁.1 Re e₁ R l₁ hγ hz x hx, mul_zero]
  obtain ⟨L, s, nb, mb, Wb, C₅, C, t₀, hL, hsec, hsnc, hnorm, hbd, ht₁, -, hm, -⟩ :=
    GlobalTheory.T.common_resolution_potential_comparison hI.pullback K' ρ' _ J' d R Amp (rename v (β * rename v₁ γ)) _ σ S S π π hπ hπ hpot hpos
      (isMultiHomog_rename hb hBh) (fun h => hBn (e₀ ▸ h)) hbad hbd₁ hbd₁
  have ht₀ : 0 < t₀ := (hm (Classical.arbitrary σ)).2.1.1
  have hp₁ := GlobalTheory.T.block_pullback_herm_line K₁ J₁ K' ρ' (κ ∘ κ₁) (v ∘ v₁) hc₁.1
  choose r hr using fun a => (hp₁.1 (Re.ref a)).exists
  have hrs : ∀ a, IsSmoothHerm (r a) := fun a => hp₁.2.1 _ _ (hr a) (Re.ref_smooth a)
  have hla : ∀ t a, (l t a).a = (r a).a := fun t a => by rw [(hl t a).1, (hr a).1, Re.line_deg]
  have hx : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal y') := fun x => R.mem x x (R.mem_U x)
  have hq : ∀ a t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((l t a).h (R.lift x x)) - Real.log ((r a).h (R.lift x x)) =
      S.phT a t (π x) := fun a t h0 h1 x => by
    rw [(hl t a).2, (hr a).2, q₁ a t h0 (h1.trans ht₁) x, add_sub_cancel_left]
  have hlr : ∀ x, 1 ≤ Real.log (rW L s x) := fun x =>
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (rW_ge L s hnorm x))).2 (rW_ge L s hnorm x)
  have hph : ∀ a, ∀ x ∉ bdry s, |S.ph a (π x)| ≤ |C₅| * Real.log (rW L s x) := fun a x hx => by
    have h1 : _ ≤ S.ph a (π x) ∧ S.ph a (π x) ≤ _ := (hm a).1.2.2.2 x hx
    have := hlr x
    rw [abs_le]
    constructor <;> nlinarith [le_abs_self C₅, abs_nonneg C₅, h1.1, h1.2]
  have hpT : ∀ a t, 0 < t → t ≤ t₀ → ∀ x ∉ bdry s, |S.phT a t (π x)| ≤ (|C| + |C₅|) * Real.log (rW L s x) ∧
      S.phT a t (π x) ≤ |C| := fun a t h0 h1 x hx => by
    obtain ⟨-, h2, h3, -⟩ := (hm a).2.1.2.2 t h0 h1
    have h4 : S.phT a t (π x) ≤ C := h2 x
    have h5 : S.ph a (π x) ≤ S.phT a t (π x) := h3 x hx
    have := hlr x
    have h6 := (abs_le.1 (hph a x hx)).1
    refine ⟨abs_le.2 ⟨?_, ?_⟩, h4.trans (le_abs_self C)⟩ <;> nlinarith [le_abs_self C, abs_nonneg C₅, abs_nonneg C]
  obtain ⟨ref, Cb, hrefs, hev, hun⟩ := hB K J II Ψ Ω W D Hd M Sr B K' ρ' _ J' d R _ _ _ Mt hSr hc₂.1 e₂ hpot hpos hMt
  obtain ⟨L₁, hL₁⟩ := ((GlobalTheory.T.block_pullback_herm_line K₁ J₁ K₃ ρ κ₁ v₁ hb₁).1 Sg).exists
  obtain ⟨L₂, hL₂⟩ := ((GlobalTheory.T.block_pullback_herm_line K J K₃ ρ κ₂ v₂ hb₂).1 (muVert Hd B)).exists
  obtain ⟨f, g, hfg, hdef⟩ := hiso L₁ L₂ hL₁ hL₂
  have hcr := (GlobalTheory.T.iso_line_on_equivalence K' ρ' _ ∅ har'.2.1 (Set.empty_subset _)).2.2.2 K₁ J₁ _ _ σ Re.ref r m hc₁.1 hr
  have hfg' : IsLineIso (mCoordIdeal y') (Top.combLine r m).a ref.a (rename v f) (rename v g) := by
    obtain ⟨t, ht⟩ := hev.exists
    rw [hcr.1, ← hSa, hc₁.2, ← hL₁.1, ← ht.2.1, (hMt t).1, hc₂.2, muReg, smoothRep_a]
    have := (GlobalTheory.T.line_isomorphism_groupoid_laws K₃ ρ _ har.2.1).2.2.2.2 K' ρ' κ v _ hb e₀ _ _ _ _ hfg
    rwa [hL₂.1] at this
  obtain ⟨w, hw, -, hws⟩ := GlobalTheory.T.line_isomorphism_defect_function K' ρ' _ J' d R _ ref _ _ har'.2.1 hfg' ((GlobalTheory.T.hermitian_combination_smooth_conj K' ρ' σ r m).1 hrs) hrefs
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn (OneModel.continuous_of_smooth R.A hws).continuousOn
  have hB₀' : ∀ x, |w (R.lift x x)| ≤ |B₀| := fun x => (hB₀ x trivial).trans (le_abs_self _)
  have hmain : ∀ x ∉ bdry s, (fun p => R.lift x x ((v ∘ v₂) p)) ∉ D.Bd ∧ w (R.lift x x) = ∑ a, (m a : ℝ) * S.ph a (π x) +
      Real.log (ref.h (R.lift x x)) - Real.log ((muVert Hd B).h fun p => R.lift x x ((v ∘ v₂) p)) := by
    intro x hxb
    have hz' : (fun p => R.lift x x (v p)) ∈ mcPts (mCoordIdeal y) := e₀ ▸ (GlobalTheory.T.block_pullback_herm_line K₃ ρ K' ρ' κ v hb).2.2.1 _ _ (hx x)
    have hne : evC (R.lift x x) (rename v (β * rename v₁ γ)) ≠ 0 := fun h => hxb ((hbd x).2 h)
    have hβ' : evC (fun p => R.lift x x (v p)) β ≠ 0 := fun h => hne (by rw [hB0, h, zero_mul])
    refine ⟨hbd₂ _ hz' hβ', ?_⟩
    have hm1 : (fun p => R.lift x x ((v ∘ v₁) p)) ∈ mcPts P₁ := e₁ ▸ hp₁.2.2.1 _ _ (hx x)
    obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.log_resolution_covers_complex_points K₁ J₁ _ _ d Re.R Re.arith _ hm1
    have ε₁ : π x = Re.π x₁ := l₁ x x₁ hx₁
    obtain ⟨u, u', huu, hu, hu'⟩ := OneModel.exists_pair_ne hfg.2 hz'
    have k₁ := hdef _ ⟨hz', hβ'⟩ u u' huu hu
    have k₂ := hw _ (hx x) (rename v u) (rename v u') (by
      have h' : u * f - u' * g ∈ imageZ v (mCoordIdeal y') := e₀ ▸ huu
      have : rename v (u * f - u' * g) ∈ mCoordIdeal y' := h'
      simpa using this) (by rw [evC_rename]; exact hu)
    rw [evC_rename, evC_rename, log_defect hu' hu (ref.pos _ (hx x).1) (HermLine.pos _ _ (hx x).1), hcr.2] at k₂
    rw [log_defect hu' hu (L₂.pos _ hz'.1) (L₁.pos _ hz'.1), hL₁.2, hL₂.2] at k₁
    have k₃ := log_diff_orbit hSa hm1.1 hx₁
    rw [hSh x₁ (fun h => hne (hbd₁ x (ε₁ ▸ h))), log_comb _ _ (Re.R.mem x₁ x₁ (Re.R.mem_U x₁)).1, ← ε₁] at k₃
    simp only [mul_add, Finset.sum_add_distrib, Function.comp_apply] at k₁ k₂ k₃ ⊢
    linarith
  have hcomb : ∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((Top.combLine (fun o : Option σ => o.elim (SheetDecomposition.PF.cst ρ') (l t))
      fun o => o.elim 0 m).h (R.lift x x)) - Real.log ((Top.combLine r m).h (R.lift x x)) =
      ∑ a, (m a : ℝ) * S.phT a t (π x) := fun t h0 h1 x => by
    rw [log_comb _ _ (hx x).1, log_comb _ _ (hx x).1, Fintype.sum_option]
    simp only [Option.elim, Int.cast_zero, zero_mul, zero_add, ← hq _ t h0 h1 x, mul_sub, Finset.sum_sub_distrib]
  have hsm : (0 : ℝ) ≤ ∑ a, |(m a : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∉ bdry s, |Real.log ((Mt t).h (R.lift x x)) - Real.log (ref.h (R.lift x x))| ≤
      (|Cb| + (∑ a, |(m a : ℝ)|) * |C₅| + |B₀|) * Real.log (rW L s x) := by
    filter_upwards [hev] with t ht x hxb
    have h1 := ht.2.2.2.1 x
    have h2 := ht.2.2.2.2 x (hmain x hxb).1
    have h3 := (hmain x hxb).2
    have h4 := abs_le.1 (abs_sum_le m fun a => hph a x hxb)
    have h5 := abs_le.1 (hB₀' x)
    have h6 := hlr x
    have h7 := mul_nonneg hsm (abs_nonneg C₅)
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [le_abs_self Cb, abs_nonneg Cb, abs_nonneg B₀]
  refine hR hI II hII K' ρ' _ J' d a b R _ L s nb mb Wb (Option σ) _ Mt _ n (rename v f) (rename v g)
    (fun t z => w z + (Real.log ((Mt t).h z) - Real.log (ref.h z)) - (Real.log ((Top.combLine
      (fun o : Option σ => o.elim (SheetDecomposition.PF.cst ρ') (l t)) fun o => o.elim 0 m).h z) - Real.log ((Top.combLine r m).h z)))
    (|B₀| + (|Cb| + (∑ a, |(m a : ℝ)|) * |C₅| + |B₀|) + (∑ a, |(m a : ℝ)|) * (|C| + |C₅|))
    hab har' hpot hpos hL hsec hsnc hnorm ?_ ?_ ?_ ?_
  · rintro (_ | i)
    · refine ⟨SheetDecomposition.PF.cst ρ', 0, SheetDecomposition.PF.cst_smooth, Eventually.of_forall fun t => ⟨SheetDecomposition.PF.cst_smooth, rfl, ?_, fun x _ => by simp⟩⟩
      intro x j z _ u
      have : (potOf R (SheetDecomposition.PF.cst ρ') + (potOf R Amp).rsmul 0).φ x ∘ (R.A.chart j).symm = fun _ => -1 := by
        funext z
        show Real.log (Real.exp (-1)) + 0 * _ = _
        simp
      exact (this ▸ by simp [ReciprocityTheory.AnForm.levi] :
        0 ≤ ReciprocityTheory.AnForm.levi ((potOf R (SheetDecomposition.PF.cst ρ') + (potOf R Amp).rsmul 0).φ x ∘ (R.A.chart j).symm) z u)
    · refine ⟨r i, 1 + (|C| + |C₅|), hrs i, ?_⟩
      filter_upwards [Ioc_mem_nhdsGT ht₀, (tendsto_epsT C).eventually_le_const one_pos] with t ht hε
      have hs : IsSmoothHerm (l t i) := hp₁.2.1 _ _ (hl t i) (Re.line_smooth i t ht.1 (ht.2.trans ht₁))
      obtain ⟨a1, -, -, -, a2, -⟩ := (hm i).2.1.2.2 t ht.1 ht.2
      refine ⟨hs, hla t i, ?_, fun x hxb => ?_⟩
      · have hP := isPotentialAdd R.A _ _ (hm i).1.1 (isPotential_ofFun _ _ a1)
        refine psh_mono (isPotential_potOf R hs) hpot hpos (hε.trans (le_add_of_nonneg_right (by positivity))) ?_
        refine psh_of_locRe (isPotentialAdd _ _ _ (isPotential_potOf R hs) (pot_rsmul hpot _))
          (isPotentialAdd _ _ _ hP (pot_rsmul hpot _)) (fun x => LocRe.congr (p₁ i _ (hr i) x trivial) ?_) a2
        filter_upwards [(R.isOpen_U x).mem_nhds (R.mem_U x)] with z hz
        have h1 := log_diff_orbit (hla t i) (hx z).1 (R.compat x z z ⟨hz, R.mem_U z⟩)
        rw [hq i t ht.1 ht.2] at h1
        show Real.log ((l t i).h (R.lift x z)) + _ - ((S.th i).φ (π x) (π z) + S.phT i t (π z) + _) =
          Real.log ((r i).h (R.lift x z)) - (S.th i).φ (π x) (π z)
        linarith
      · have h1 := hpT i t ht.1 ht.2 x hxb
        have h2 := hlr x
        show _ ≤ Real.log ((l t i).h _) - _ ∧ Real.log ((l t i).h _) - _ ≤ _
        rw [hq i t ht.1 ht.2]
        exact ⟨by nlinarith [(abs_le.1 h1.1).1], by linarith [h1.2, abs_nonneg C₅]⟩
  · refine ⟨ref, |Cb| + (∑ a, |(m a : ℝ)|) * |C₅| + |B₀|, hrefs, ?_⟩
    have hle : Cb ≤ |Cb| + (∑ a, |(m a : ℝ)|) * |C₅| + |B₀| := by
      linarith [le_abs_self Cb, abs_nonneg B₀, mul_nonneg hsm (abs_nonneg C₅)]
    filter_upwards [hev, hlow] with t ht h1
    exact ⟨ht.1, ht.2.1, psh_mono (isPotential_potOf R ht.1) hpot hpos hle ht.2.2.1,
      fun x hxb => ⟨by linarith [(abs_le.1 (h1 x hxb)).1], (ht.2.2.2.1 x).trans hle⟩⟩
  · filter_upwards [hev, hlow, Ioc_mem_nhdsGT ht₀] with t ht h1 h2
    refine ⟨?_, fun z hz u u' huu hu => ?_, fun x hxb => ?_⟩
    · convert hfg' using 1
      · simp only [Top.combLine, Fintype.sum_option, Option.elim, zero_smul, zero_add, hla]
      · exact ht.2.1
    · have hu' := den_ne har'.2.1.1 hfg'.2 hz huu hu
      beta_reduce
      rw [hw z hz u u' huu hu, log_defect hu' hu (ref.pos _ hz.1) (HermLine.pos _ _ hz.1),
        log_defect hu' hu ((Mt t).pos _ hz.1) (HermLine.pos _ _ hz.1)]
      ring
    · rw [hcomb t h2.1 h2.2]
      have h3 := abs_le.1 (abs_sum_le m fun a => (hpT a t h2.1 h2.2 x hxb).1)
      have h4 := abs_le.1 (h1 x hxb)
      have h5 := abs_le.1 (hB₀' x)
      have h6 := mul_le_mul_of_nonneg_left (hlr x) (abs_nonneg B₀)
      refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith
  · intro K₀ hK₀ hKc
    obtain ⟨Rm, hRm⟩ := hKc.exists_bound_of_continuousOn ((rW_open R.A L s hL hsec).1.mono hK₀)
    have h1 := Metric.tendstoUniformlyOn_iff.1 (hun K₀ (fun x hx => (hmain x (hK₀ hx)).1) hKc)
    have h2 : Tendsto (fun t : ℝ => (∑ a, |(m a : ℝ)|) * (t ^ ((1 : ℝ) / 3) + |epsT C t| * Rm)) (𝓝[>] 0) (𝓝 0) := by
      have a1 : Tendsto (fun t : ℝ => t ^ ((1 : ℝ) / 3)) (𝓝[>] 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (1 / 3) (Or.inr (by norm_num))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        rwa [Real.zero_rpow (by norm_num)] at this
      simpa using (a1.add ((tendsto_epsT C).abs.mul_const Rm)).const_mul (∑ a, |(m a : ℝ)|)
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [h1 _ (half_pos hε), h2.eventually_lt_const (half_pos hε), Ioc_mem_nhdsGT ht₀] with t a1 a2 a3 x hxK
    have b1 := a1 x hxK
    have b2 : ∀ i, |S.phT i t (π x) - S.ph i (π x)| ≤ t ^ ((1 : ℝ) / 3) + |epsT C t| * Rm := fun i => by
      obtain ⟨-, -, c1, -, -, -, c2, -⟩ := (hm i).2.1.2.2 t a3.1 a3.2
      have c3 : S.ph i (π x) ≤ S.phT i t (π x) := c1 x (hK₀ hxK)
      have c4 : S.phT i t (π x) ≤ S.ph i (π x) + _ + _ := c2 x (hK₀ hxK)
      have c5 : epsT C t * rW L s x ≤ |epsT C t| * Rm := (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hRm x hxK) (abs_nonneg _))
      rw [abs_of_nonneg (sub_nonneg.2 c3)]
      linarith
    have b3 := abs_le.1 (abs_sum_le m b2)
    rw [Real.dist_eq, abs_lt] at b1 ⊢
    rw [hcomb t a3.1 a3.2, (hmain x (hK₀ hxK)).2]
    simp only [mul_sub, Finset.sum_sub_distrib] at b3
    constructor <;> linarith [b1.1, b1.2, b3.1, b3.2]

end LevelTowerAlt.Comparison₂
