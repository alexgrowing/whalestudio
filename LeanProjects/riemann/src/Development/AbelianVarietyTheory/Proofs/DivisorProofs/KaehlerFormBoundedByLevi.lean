import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly

set_option autoImplicit false
noncomputable section
open Filter Topology Set ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KaehlerCmp

theorem levi_le_mul_eventually {e : ℕ} {f g : (Fin e → ℂ) → ℝ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (hg : ContDiffOn ℝ 2 g V) (hp : ∀ z ∈ V, ∀ w, w ≠ 0 → 0 < levi g z w)
    {z₀ : Fin e → ℂ} (hz : z₀ ∈ V) : ∃ K : ℝ, ∀ᶠ z in 𝓝 z₀, ∀ w, levi f z w ≤ K * levi g z w := by
  obtain ⟨C, hCn, hCV, hC⟩ := local_compact_nhds (hV.mem_nhds hz)
  have hS : IsCompact (C ×ˢ Metric.sphere (0 : Fin e → ℂ) 1) := hC.prod (isCompact_sphere _ _)
  have hsub : C ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 ⊆ V ×ˢ univ := prod_mono hCV (subset_univ _)
  have hne : ∀ u ∈ Metric.sphere (0 : Fin e → ℂ) 1, u ≠ 0 := fun u hu h => by simp [h] at hu
  have hc : ContinuousOn (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi f q.1 q.2 / levi g q.1 q.2)
      (C ×ˢ Metric.sphere (0 : Fin e → ℂ) 1) :=
    ((continuousOn_levi hV hf).mono hsub).div ((continuousOn_levi hV hg).mono hsub)
      fun q hq => (hp _ (hCV hq.1) _ (hne _ hq.2)).ne'
  obtain ⟨K, hK⟩ := hS.bddAbove_image hc
  refine ⟨K, mem_of_superset hCn fun z hzC w => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp [levi_zero]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hu : (‖w‖⁻¹ : ℝ) • w ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
    simp [norm_smul, hn]
  have h1 : levi f z ((‖w‖⁻¹ : ℝ) • w) / levi g z ((‖w‖⁻¹ : ℝ) • w) ≤ K :=
    hK (mem_image_of_mem _ (show (z, (‖w‖⁻¹ : ℝ) • w) ∈ C ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 from ⟨hzC, hu⟩))
  rw [levi_smul_dir, levi_smul_dir, mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hn)),
    div_le_iff₀ (hp z (hCV hzC) w hw)] at h1
  exact h1

section

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
  {R : AnRead p σ d} {a b : ChartForm p σ d}

theorem kaehler_nonneg (ha : IsKaehlerForm R a) (c : AlgChart p σ d) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (ξ : Fin d → ℂ) : 0 ≤ a c y ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · obtain ⟨W, φ, hW, ho, hs, e⟩ := ha.1 y
    rw [e c y hy hW, ddcForm, AlgChart.levi, c.leviV_re_eq (hs.contDiffAt_two ho hy hW), levi_zero, zero_div]
  · exact (ha.2 c y hy ξ hξ).le

theorem kaehler_le_eventually (ha : IsKaehlerForm R a) (hb : IsKaehlerForm R b) (y₀ : CxPts p σ) :
    ∃ K : ℝ, ∀ᶠ y in 𝓝 y₀, ∀ c : AlgChart p σ d, y ∈ c.e.source → ∀ ξ, a c y ξ ≤ K * b c y ξ := by
  obtain ⟨j, hj⟩ := R.cover y₀
  set c₀ := R.chart j
  obtain ⟨W, φ, hW, ho, hs, e⟩ := ha.1 y₀
  obtain ⟨W', ψ, hW', ho', hs', e'⟩ := hb.1 y₀
  have hV : IsOpen (c₀.finChart.target ∩ c₀.finChart.symm ⁻¹' (W ∩ W')) :=
    c₀.finChart.isOpen_inter_preimage_symm (ho.inter ho')
  have hval : ∀ {a : ChartForm p σ d} {W φ}, ShFam.IsPotential R a W φ → ∀ y ∈ c₀.e.source, y ∈ W → ∀ ξ,
      a c₀ y ξ = levi (φ ∘ c₀.finChart.symm) (c₀.finChart y) ξ / Real.pi := fun h y hy hyW ξ => by
    rw [h.2.2 c₀ y hy hyW, ddcForm, AlgChart.levi, c₀.leviV_re_eq (h.2.1.contDiffAt_two h.1 hy hyW)]
  have hl : c₀.finChart.symm (c₀.finChart y₀) = y₀ := c₀.finChart.left_inv hj
  obtain ⟨K, hK⟩ := levi_le_mul_eventually (f := φ ∘ c₀.finChart.symm) (g := ψ ∘ c₀.finChart.symm) hV
    (((c₀.contDiffOn_finChart_iff _ _ _).2 (hs.mono inter_subset_left j)).of_le (WithTop.coe_le_coe.2 le_top))
    (((c₀.contDiffOn_finChart_iff _ _ _).2 (hs'.mono inter_subset_right j)).of_le (WithTop.coe_le_coe.2 le_top))
    (fun z hz w hw => by
      have h1 := hb.2 c₀ _ (c₀.finChart.map_target hz.1) w hw
      rw [hval ⟨ho', hs', e'⟩ _ (c₀.finChart.map_target hz.1) hz.2.2, c₀.finChart.right_inv hz.1] at h1
      exact (div_pos_iff_of_pos_right Real.pi_pos).1 h1)
    (z₀ := c₀.finChart y₀) ⟨c₀.finChart.map_source hj, by rw [mem_preimage, hl]; exact ⟨hW, hW'⟩⟩
  refine ⟨K, ?_⟩
  filter_upwards [(c₀.finChart.continuousAt hj).eventually hK, c₀.e.open_source.mem_nhds hj, ho.mem_nhds hW,
    ho'.mem_nhds hW'] with y h1 h2 h3 h4 c hy ξ
  rw [ha.trans hy h2, hb.trans hy h2, hval ⟨ho, hs, e⟩ y h2 h3, hval ⟨ho', hs', e'⟩ y h2 h4, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h1 _) Real.pi_pos.le

theorem kaehler_le_mul [CompactSpace (CxPts p σ)] (ha : IsKaehlerForm R a) (hb : IsKaehlerForm R b) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, a c y ξ ≤ K * b c y ξ := by
  have hm : ∀ {K K' : ℝ} {y}, K ≤ K' → (∀ c : AlgChart p σ d, y ∈ c.e.source → ∀ ξ, a c y ξ ≤ K * b c y ξ) →
      ∀ c : AlgChart p σ d, y ∈ c.e.source → ∀ ξ, a c y ξ ≤ K' * b c y ξ := fun hK h c hy ξ =>
    (h c hy ξ).trans (mul_le_mul_of_nonneg_right hK (kaehler_nonneg hb c hy ξ))
  obtain ⟨K, hK⟩ := isCompact_univ.induction_on
    (p := fun S : Set (CxPts p σ) => ∃ K : ℝ, ∀ y ∈ S, ∀ c : AlgChart p σ d, y ∈ c.e.source →
      ∀ ξ, a c y ξ ≤ K * b c y ξ)
    ⟨0, fun _ h => h.elim⟩ (fun _ _ h ⟨K, hK⟩ => ⟨K, fun y hy => hK y (h hy)⟩)
    (fun _ _ ⟨K, hK⟩ ⟨K', hK'⟩ => ⟨max K K', fun y hy =>
      hy.elim (fun h => hm (le_max_left _ _) (hK y h)) fun h => hm (le_max_right _ _) (hK' y h)⟩)
    fun y _ => by
      obtain ⟨K, hK⟩ := kaehler_le_eventually ha hb y
      exact ⟨_, mem_nhdsWithin_of_mem_nhds hK, K, fun _ h => h⟩
  exact ⟨max K 1, lt_max_of_lt_right one_pos, fun c y hy => hm (le_max_left _ _) (hK y trivial) c hy⟩

end

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {M : Man Y.dim} (I : ManIs M Y) (a : Fin (M.n + 1))

theorem smoothOn_of_man {U : Set (M.X a)} (hU : IsOpen U) {G : M.X a → ℝ} (hG : (M.A a).SmoothOn U G) :
    (Y.an (I.ε a)).SmoothOn ((I.pt a).symm ⁻¹' U) (fun y => G ((I.pt a).symm y)) := by
  have hcov : ∀ y : Pts Y (I.ε a), ∃ j, y ∈ ((I.alg a j).choose).e.source := by
    intro y
    obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
    refine ⟨j, ?_⟩
    rw [(I.alg a j).choose_spec] at hj
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using hj
  let R : AnRead Y.str (I.ε a) Y.dim := ⟨Fin (M.A a).n, fun j => (I.alg a j).choose, hcov⟩
  refine (AnRead.smoothOn_iff R (Y.an (I.ε a)) (hU.preimage (I.pt a).symm.continuous)).1 fun j => ?_
  have h1 := hG j
  rw [(I.alg a j).choose_spec] at h1
  exact ((I.alg a j).choose.contDiffOn_finChart_iff _ _ _).1 h1

theorem exists_levi_eq_leviAt (c : AlgChart Y.str (I.ε a) Y.dim) {y : Pts Y (I.ε a)} (hy : y ∈ c.e.source)
    (ξ : Fin Y.dim → ℂ) : ∃ j, ∃ v ∈ ((M.A a).chart j).target, ∃ w, (ξ ≠ 0 → w ≠ 0) ∧
      ∀ P : LocPot (M.X a), ReciprocityTheory.AnForm.M.IsPotential (M.A a) P → ∀ x, (I.pt a).symm y ∈ P.U x →
        c.levi (fun z => P.φ x ((I.pt a).symm z)) y ξ = leviAt (M.A a) P j v w := by
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨cj, hcj⟩ := I.alg a j
  have hyj : y ∈ cj.e.source := by
    rw [hcj] at hj
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using hj
  have hv := ((M.A a).chart j).map_source hj
  have hvc : (M.A a).chart j ((I.pt a).symm y) = cj.finChart y := by
    rw [hcj]
    simp
  refine ⟨j, _, hv, c.dtrans cj y ξ, AlgChart.dtrans_ne_zero hy hyj, fun P hP x hx => ?_⟩
  have hG : ContDiffAt ℝ 2 ((fun z => P.φ x ((I.pt a).symm z)) ∘ cj.e.symm) (cj.e y) :=
    (smoothOn_of_man I a (P.isOpen_U x) (hP.1 x)).contDiffAt_two
      ((P.isOpen_U x).preimage (I.pt a).symm.continuous) hyj hx
  rw [AlgChart.levi_trans hy hyj hG,
    ← GlobalTheory.ShellMass.levi_base hP x j hv (by rw [((M.A a).chart j).left_inv hj]; exact hx),
    hvc, AlgChart.levi, cj.leviV_re_eq hG, hcj]
  congr 1

theorem kaehler_le_levi_Om : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y),
    Y.dim = e → ∀ (a : Fin (M.n + 1)) (om : ChartForm Y.str (I.ε a) Y.dim), IsKaehlerForm (Y.an (I.ε a)) om →
    ∃ K : ℝ, 0 < K ∧ ∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ x, (I.pt a).symm y ∈ (M.Om a).U x →
      ∀ ξ, 0 ≤ c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ ∧
        om c y ξ ≤ K * c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ := by
  intro F _ _ Y e M I he a om hom
  subst he
  have hP := (M.bd a).2.2.1
  have hpos := (M.bd a).2.2.2.1
  haveI : CompactSpace (Pts Y (I.ε a)) := (I.pt a).compactSpace
  let b : ChartForm Y.str (I.ε a) Y.dim := fun c y =>
    ddcForm (fun z => (M.Om a).φ ((I.pt a).symm y) ((I.pt a).symm z)) c y
  have hb : ∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ x, (I.pt a).symm y ∈ (M.Om a).U x → ∀ ξ,
      b c y ξ = ddcForm (fun z => (M.Om a).φ x ((I.pt a).symm z)) c y ξ := by
    intro c y hy x hx ξ
    obtain ⟨j, v, -, w, -, h⟩ := exists_levi_eq_leviAt I a c hy ξ
    simp only [b, ddcForm]
    rw [h _ hP x hx, h _ hP _ ((M.Om a).mem_U _)]
  have hk : IsKaehlerForm (Y.an (I.ε a)) b := by
    refine ⟨fun y => ⟨_, _, (M.Om a).mem_U ((I.pt a).symm y),
      ((M.Om a).isOpen_U _).preimage (I.pt a).symm.continuous,
      smoothOn_of_man I a ((M.Om a).isOpen_U _) (hP.1 _), fun c z hz hx => hb c z hz _ hx⟩, fun c y hy ξ hξ => ?_⟩
    obtain ⟨j, v, hv, w, hw, h⟩ := exists_levi_eq_leviAt I a c hy ξ
    simp only [b, ddcForm]
    rw [h _ hP _ ((M.Om a).mem_U _)]
    exact div_pos (hpos _ j v ⟨hv, (M.Om a).mem_U _⟩ w (hw hξ)) Real.pi_pos
  obtain ⟨K, hK, h⟩ := kaehler_le_mul hom hk
  refine ⟨K / Real.pi, div_pos hK Real.pi_pos, fun c y hy x hx ξ => ⟨?_, ?_⟩⟩
  · have h0 := kaehler_nonneg hk c hy ξ
    rw [hb c y hy x hx, ddcForm] at h0
    simpa only [zero_mul] using (le_div_iff₀ Real.pi_pos).1 h0
  · have h0 := h c y hy ξ
    rw [hb c y hy x hx, ddcForm] at h0
    refine h0.trans_eq ?_
    ring

end GlobalTheory.KaehlerCmp
