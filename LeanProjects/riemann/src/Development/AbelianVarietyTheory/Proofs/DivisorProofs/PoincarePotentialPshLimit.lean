import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPlurisubharmonicCorrectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSetupCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfMetWeightEqPotentialHolo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArDegIndep.CurvOther

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4O.CombForm
open scoped ContDiff

section Norms

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem eventually_sq_le {R : AnRead p σ d} {C : Closeds Y} {n n' : CxPts p σ → ℝ} (hn : IsDivNorm R C n)
    (hn' : IsDivNorm R C n') (y₀ : CxPts p σ) : ∃ K : ℝ, ∀ᶠ y in 𝓝 y₀, n y ^ 2 ≤ K * n' y ^ 2 := by
  obtain ⟨V, t, f, hy, ht, hf, e⟩ := hn.2 y₀
  obtain ⟨V', t', f', hy', ht', hf', e'⟩ := hn'.2 y₀
  have hx : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ V.1 ⊓ V'.1 := ⟨mem_ptsIn.1 hy, mem_ptsIn.1 hy'⟩
  obtain ⟨h, hhW, hxh⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ V'.1) ⟨_, hx⟩ hx.1
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, V.2.basicOpen h⟩
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_left
  have hWV' : Wa.1 ≤ V'.1 := hhW.trans inf_le_right
  have hy0W : y₀ ∈ ptsIn p σ Wa.1 := mem_ptsIn.2 hxh
  have e1 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y hWV t} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, ht, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : (Scheme.IdealSheafData.vanishingIdeal C).ideal Wa = Ideal.span {resG Y hWV' t'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V') hWV', ht', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 ((e1.symm.trans e2).le (Ideal.subset_span rfl))
  have hev : ∀ z ∈ ptsIn p σ Wa.1, ev p σ V.1 t z = ev p σ Wa.1 u z * ev p σ V'.1 t' z := by
    intro z hz
    rw [← ev_res hWV hz, ← hu, ev_mul, ev_res hWV' hz]
  let g : CxPts p σ → ℝ := fun z => ‖ev p σ Wa.1 u z‖ ^ 2 * Real.exp (f' z - f z)
  have hg : ContinuousOn g (ptsIn p σ Wa.1) :=
    ((continuousOn_ev _).norm.pow 2).mul (((hf'.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV')).sub
      ((hf.continuousOn (isOpen_ptsIn _)).mono (ptsIn_mono hWV))).rexp
  have hW := (isOpen_ptsIn (p := p) (σ := σ) Wa.1).mem_nhds hy0W
  refine ⟨g y₀ + 1, ?_⟩
  filter_upwards [hW, (hg.continuousAt hW).eventually (eventually_le_nhds (lt_add_one (g y₀)))] with z hz hz'
  have : n z ^ 2 = g z * n' z ^ 2 := by
    rw [e z (ptsIn_mono hWV hz), e' z (ptsIn_mono hWV' hz), hev z hz, norm_mul, mul_pow]
    simp only [g, Real.exp_sub, Real.exp_neg]
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hz' (sq_nonneg _)

theorem exists_sq_le [CompactSpace (CxPts p σ)] {R : AnRead p σ d} {C : Closeds Y} {n n' : CxPts p σ → ℝ}
    (hn : IsDivNorm R C n) (hn' : IsDivNorm R C n') : ∃ K : ℝ, 1 ≤ K ∧ ∀ y, n y ^ 2 ≤ K * n' y ^ 2 := by
  choose K hK using eventually_sq_le hn hn'
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover _ fun y _ => hK y
  have h0 : 0 ≤ ∑ x ∈ s, |K x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨1 + ∑ x ∈ s, |K x|, by linarith, fun y => ?_⟩
  obtain ⟨x, hx, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  have := (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |K x|) (fun _ _ => abs_nonneg _) hx)
  exact le_trans h (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end Norms

theorem exists_eq_of_compList {X : Scheme.{0}} {B : Set X} {m m' : ℕ} {C : Fin m → Closeds X} {C' : Fin m' → Closeds X}
    (hC : R.FinalTheorems.CompList B C) (hC' : R.FinalTheorems.CompList B C') (i : Fin m') : ∃ j, C j = C' i := by
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 (hC'.1 i))
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine (Set.subset_iUnion (fun j => (C' j : Set X)) i).trans (hC'.2.1.le.trans
        (hC.2.1.ge.trans (Set.iUnion_subset fun j => ?_)))
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨j, SetLike.coe_injective (((GlobalTheory.SncLocal.mem_comps_of_compList hC' i).2
    (GlobalTheory.SncLocal.mem_comps_of_compList hC j).1 hDz).antisymm hDz)⟩

theorem exists_log_r_le {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x x' : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : ∃ K : ℝ, 0 < K ∧ ∀ y, ¬ LiesIn y (genBd s.T.Z) → Real.log (x'.r σ y) ≤ K * Real.log (x.r σ y) := by
  have : CompactSpace (CxPts (genStr s.T.Z) σ) :=
    CxPts.compactSpace σ (ProjSpace.isProjOver_pullback_snd _ s.T.Z.proj)
  choose J hJ using exists_eq_of_compList x.cpt_list x'.cpt_list
  choose K hK1 hK using fun i => exists_sq_le (x.nrm_div σ (J i)) (hJ i ▸ x'.nrm_div σ i)
  let c : ℝ := 1 + ∑ i, (1 + Real.log (K i))
  have hc0 : 0 ≤ ∑ i, (1 + Real.log (K i)) := Finset.sum_nonneg fun i _ => by linarith [Real.log_nonneg (hK1 i)]
  have hc : 1 ≤ c := by simp only [c]; linarith
  refine ⟨1 + Real.log c, by linarith [Real.log_nonneg hc], fun y hy => ?_⟩
  have hr := x.exp_le_r σ y
  have hr' := x'.exp_le_r σ y
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hl : 1 ≤ Real.log (x.r σ y) := (Real.le_log_iff_exp_le (by linarith)).2 hr
  have hs (x : ToroidalCompactificationData s) : x.r σ y = Real.exp 1 + ∑ i, -Real.log (x.nrm σ i y ^ 2) := by
    rw [OddPrimesWithRootsOfUnity.r, ← Finset.prod_pow, Real.log_prod fun i _ => (pow_pos (x.nrm_pos hy i) 2).ne', Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have h1 (i) : -Real.log (x.nrm σ i y ^ 2) ≤ x.r σ y := by
    have := Finset.single_le_sum (f := fun i => -Real.log (x.nrm σ i y ^ 2)) (fun i _ => neg_nonneg.2
      (Real.log_nonpos (sq_nonneg _) (pow_le_one₀ ((x.nrm_div σ i).1 y).1 ((x.nrm_div σ i).1 y).2))) (Finset.mem_univ i)
    rw [hs x]
    linarith
  have h2 (i) : -Real.log (x'.nrm σ i y ^ 2) ≤ (1 + Real.log (K i)) * x.r σ y := by
    have a := Real.log_le_log (pow_pos (x.nrm_pos hy _) 2) (hK i y)
    rw [Real.log_mul (by linarith [hK1 i]) (pow_pos (x'.nrm_pos hy _) 2).ne'] at a
    nlinarith [h1 (J i), Real.log_nonneg (hK1 i)]
  have h3 : x'.r σ y ≤ c * x.r σ y := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
    rw [← Finset.sum_mul] at this
    rw [hs x']
    simp only [c]
    linarith
  have h4 := Real.log_le_log (by linarith) h3
  rw [Real.log_mul (by linarith) (by linarith)] at h4
  nlinarith [Real.log_nonneg hc]

section Levi

variable {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {A : FinHolAtlas e X}
  {A' : FinHolAtlas e' X'}

theorem levi_add' {ι : Type} [Fintype ι] {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : ι → ℂ) : levi (fun v => f v + g v) z w = levi f z w + levi g z w := by
  simpa using levi_add_smul 1 hf hg w

theorem contDiffAt_two_comp_chart_symm_of_smoothOn {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) {k : Fin A.n}
    {v : Fin e → ℂ} (hv : v ∈ (A.chart k).target) (hvU : (A.chart k).symm v ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart k).symm) v :=
  ((hf k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨hv, hvU⟩)).of_le
    (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

theorem levi_pull {g : X → X'} (hg : HoloMap A A' g) {f : X' → ℝ} {j : Fin A.n} {k : Fin A'.n} {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hk : g ((A.chart j).symm y) ∈ (A'.chart k).source)
    (hf : ContDiffAt ℝ 2 (f ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y)))) (w : Fin e → ℂ) :
    ContDiffAt ℝ 2 (fun v => f (g ((A.chart j).symm v))) y ∧
      levi (fun v => f (g ((A.chart j).symm v))) y w = levi (f ∘ (A'.chart k).symm)
        (A'.chart k (g ((A.chart j).symm y))) (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) := by
  have hτ : AnalyticAt ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y := hg.2 j k y ⟨hy, hk⟩
  have hev : (fun v => f (g ((A.chart j).symm v))) =ᶠ[𝓝 y]
      (f ∘ (A'.chart k).symm) ∘ (A'.chart k ∘ g ∘ (A.chart j).symm) := by
    filter_upwards [holoMap_preimage_mem_nhds hg j k hy hk] with y' hy'
    simp only [Function.comp_apply, (A'.chart k).left_inv hy'.2]
  refine ⟨?_, (levi_congr hev w).trans (levi_comp w hτ hf)⟩
  exact (ContDiffAt.comp (g := f ∘ (A'.chart k).symm) y hf hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq hev

theorem smoothOn_pull {g : X → X'} (hg : HoloMap A A' g) {U : Set X'} (hU : IsOpen U) {f : X' → ℝ}
    (hf : A'.SmoothOn U f) : A.SmoothOn (g ⁻¹' U) (f ∘ g) := fun j y hy => by
  obtain ⟨k, hk⟩ := A'.cover (g ((A.chart j).symm y))
  have hτ : AnalyticAt ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y := hg.2 j k y ⟨hy.1, hk⟩
  have hf' : ContDiffAt ℝ ∞ (f ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y))) :=
    (hf k).contDiffAt (((A'.chart k).isOpen_inter_preimage_symm hU).mem_nhds
      ⟨(A'.chart k).map_source hk, by rw [Set.mem_preimage, (A'.chart k).left_inv hk]; exact hy.2⟩)
  have hev : (f ∘ g) ∘ (A.chart j).symm =ᶠ[𝓝 y]
      (f ∘ (A'.chart k).symm) ∘ (A'.chart k ∘ g ∘ (A.chart j).symm) := by
    filter_upwards [holoMap_preimage_mem_nhds hg j k hy.1 hk] with y' hy'
    simp only [Function.comp_apply, (A'.chart k).left_inv hy'.2]
  exact ((ContDiffAt.comp (g := f ∘ (A'.chart k).symm) y hf' hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq
    hev).contDiffWithinAt

end Levi

section Transfer

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {e e' : ℕ} {X X' : Type} [TopologicalSpace X]
  [TopologicalSpace X'] {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'}

theorem lnRatio_germ (pt : X ≃ₜ Pts Y σ) (pt' : X' ≃ₜ Pts Y σ) (hA : IsAlgAtlas (tAtlas A pt)) {g : X → X'}
    (hgpt : ∀ z, pt' (g z) = pt z) {Δ : Y.Dv} {m m' : (cxSt F).Met Y σ Δ} (hm : ∀ v, PosAt m v) (hm' : ∀ v, PosAt m' v)
    {Q : LocPot X} (hQ : IsPot pt m Q) {Q' : LocPot X'} (hQ' : IsPot pt' m' Q') {j : Fin A.n} {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G y ∧
      (fun v => lnRatio m' m (pt ((A.chart j).symm v))) =ᶠ[𝓝 y] fun v =>
        Q.φ ((A.chart j).symm y) ((A.chart j).symm v) + (-1) * Q'.φ (g ((A.chart j).symm y)) (g ((A.chart j).symm v)) +
          (G v).re := by
  set z := (A.chart j).symm y
  set x0 := pt z
  have hg' : ∀ z, g z = pt'.symm (pt z) := fun z => by rw [← hgpt z, Homeomorph.symm_apply_apply]
  have hc := mem_pick (isLB_toLB Δ) x0
  obtain ⟨W, hW, hxW, G, hG, hGe⟩ := GlobalTheory.Adopt.half_metWeight_eq_potential_holo F (cxSt F) Y σ e (tAtlas A pt) hA Δ m hm
    (Q.pullback pt.symm pt.symm.continuous) (IsPot.pullback_symm hQ) x0 _ hc
  obtain ⟨W', hW', hxW', G', hG', hGe'⟩ := GlobalTheory.Adopt.half_metWeight_eq_potential_holo F (cxSt F) Y σ e (tAtlas A pt) hA Δ m' hm'
    (Q'.pullback pt'.symm pt'.symm.continuous) (IsPot.pullback_symm hQ') x0 _ hc
  have hS : IsOpen (pt ⁻¹' (W ∩ W' ∩ ptsIn Y.str σ ((toLB Δ).U (pick (isLB_toLB Δ) x0)))) :=
    ((hW.inter hW').inter (isOpen_ptsIn _)).preimage pt.continuous
  refine ⟨fun v => G (pt ((A.chart j).symm v)) - G' (pt ((A.chart j).symm v)), ?_, ?_⟩
  · exact (hG j y ⟨hy, hxW⟩).sub (hG' j y ⟨hy, hxW'⟩)
  · filter_upwards [((A.chart j).isOpen_inter_preimage_symm hS).mem_nhds ⟨hy, ⟨hxW, hxW'⟩, hc⟩] with v hv
    obtain ⟨-, ⟨hv1, hv2⟩, hv3⟩ := hv
    set q := pt ((A.chart j).symm v)
    have e1 := hGe q hv1
    have e2 := hGe' q hv2
    have hq : under q ∈ ((toLB Δ).U (pick (isLB_toLB Δ) x0)) := mem_ptsIn.1 hv3
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 ((pick (isLB_toLB Δ) x0).2.2 _ hq)
    rw [lnRatio_eq hgen (hm' q) (hm q)]
    simp only [LocPot.pullback, metWeight_φ, Homeomorph.symm_apply_apply, q, x0] at e1 e2
    simp only [lnN, hg', Complex.sub_re]
    linarith

end Transfer

section Main

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {e e' : ℕ} {X X' : Type} [TopologicalSpace X]
  [TopologicalSpace X'] {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'}

theorem isPoin_pull {g : X → X'} (hg : HoloMap A A' g) {Z : Set X} {Z' : Set X'} (hZc : IsClosed Z')
    (hZZ : ∀ z, z ∈ Z ↔ g z ∈ Z') {r : X → ℝ} {r' : X' → ℝ} {K : ℝ} (hK : 0 < K)
    (hr : ∀ z, z ∉ Z → Real.log (r z) ≤ K * Real.log (r' (g z)))
    (hr2 : ∀ z, z ∉ Z → Real.log (r' (g z)) ≤ K * Real.log (r z)) (hr' : ∀ z, z ∉ Z → 1 ≤ Real.log (r' (g z)))
    {b' : LocPot X'} {p' : X' → ℝ} (h : IsPoin A' Z' r' b' p') :
    IsPoin A Z r (b'.pullback g hg.1) (p' ∘ g) := by
  obtain ⟨hb, hp, ⟨c, C, hc, hcC⟩, hpsh⟩ := h
  have hZe : Zᶜ = g ⁻¹' Z'ᶜ := Set.ext fun z => (hZZ z).not
  refine ⟨isPotentialPullback A' A g hg b' hb, hZe ▸ smoothOn_pull hg hZc.isOpen_compl hp,
    ⟨c / K, max C 0 * K, div_pos hc hK, fun z hz => ?_⟩, fun j y hy hz w => ?_⟩
  · have hz' : g z ∉ Z' := (hZZ z).not.1 hz
    obtain ⟨h1, h2⟩ := hcC (g z) hz'
    have a1 := hr z hz
    have a2 := hr' z hz
    have a4 := hr2 z hz
    constructor
    · have b1 : C * Real.log (r' (g z)) ≤ max C 0 * Real.log (r' (g z)) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (by linarith)
      have b2 : max C 0 * Real.log (r' (g z)) ≤ max C 0 * (K * Real.log (r z)) :=
        mul_le_mul_of_nonneg_left a4 (le_max_right C 0)
      simp only [Function.comp_apply]
      nlinarith
    · have : c / K * Real.log (r z) ≤ c * Real.log (r' (g z)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hK]
        nlinarith
      simp only [Function.comp_apply]
      linarith
  · have hz' : g ((A.chart j).symm y) ∉ Z' := (hZZ _).not.1 hz
    obtain ⟨k, hk⟩ := A'.cover (g ((A.chart j).symm y))
    have hy' := (A'.chart k).map_source hk
    have hsy := (A'.chart k).left_inv hk
    have hb2 := potential_contDiffAt_chart hb (g ((A.chart j).symm y)) k hy' (by rw [hsy]; exact b'.mem_U _)
    have hp2 := contDiffAt_two_comp_chart_symm_of_smoothOn hZc.isOpen_compl hp hy' (by rw [hsy]; exact hz')
    have key := hpsh k _ hy' (by rw [hsy]; exact hz') (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w)
    have L := levi_pull hg hy hk (f := fun x => b'.φ (g ((A.chart j).symm y)) x + p' x) (hb2.add hp2) w
    unfold leviAt at key ⊢
    rw [hsy] at key
    exact L.2.symm ▸ key

theorem pshOff_transfer (pt : X ≃ₜ Pts Y σ) (pt' : X' ≃ₜ Pts Y σ) (hA : IsAlgAtlas (tAtlas A pt)) {g : X → X'}
    (hg : HoloMap A A' g) (hgpt : ∀ z, pt' (g z) = pt z) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m m' : ∀ i, (cxSt F).Met Y σ (Δ i)) (hm : ∀ i v, PosAt (m i) v) (hm' : ∀ i v, PosAt (m' i) v)
    (Q : ι → LocPot X) (hQ : ∀ i, IsPot pt (m i) (Q i) ∧ IsPotential A (Q i))
    (Q' : ι → LocPot X') (hQ' : ∀ i, IsPot pt' (m' i) (Q' i) ∧ IsPotential A' (Q' i)) (s : ι → ℝ)
    (th : LocPot X) (hth : IsPotential A th)
    (hthQ : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A th j y w = ∑ i, s i * leviAt A (Q i) j y w)
    (th' : LocPot X') (hth' : IsPotential A' th')
    (hthQ' : ∀ j, ∀ y ∈ (A'.chart j).target, ∀ w, leviAt A' th' j y w = ∑ i, s i * leviAt A' (Q' i) j y w)
    (ψ : X → ℝ) (ψ' : X' → ℝ) (hψ' : A'.Smooth ψ')
    (hψ : ∀ z, ψ z = ψ' (g z) + ∑ i, (-s i) * lnRatio (m' i) (m i) (pt z))
    {Z : Set X} {Z' : Set X'} (hZc : IsClosed Z') (hZZ : ∀ z, z ∈ Z ↔ g z ∈ Z')
    (b' : LocPot X') (p' : X' → ℝ) (hb' : IsPotential A' b') (hp' : A'.SmoothOn Z'ᶜ p') (t : ℝ)
    (h : PshOff A' Z' (th' + LocPot.ofFun ψ' + (b' + LocPot.ofFun p').rsmul t)) :
    PshOff A Z (th + LocPot.ofFun ψ + (b'.pullback g hg.1 + LocPot.ofFun (p' ∘ g)).rsmul t) := by
  intro j y hy hz w
  have hz' : g ((A.chart j).symm y) ∉ Z' := (hZZ _).not.1 hz
  obtain ⟨k, hk⟩ := A'.cover (g ((A.chart j).symm y))
  have hy' := (A'.chart k).map_source hk
  have hsy := (A'.chart k).left_inv hk
  have key := h k _ hy' (by rw [hsy]; exact hz') (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w)

  have c1 := potential_contDiffAt_chart hth' (g ((A.chart j).symm y)) k hy' (by rw [hsy]; exact th'.mem_U _)
  have c2 := contDiffAt_two_comp_chart_symm_of_smoothOn isOpen_univ hψ' hy' trivial
  have c3 := potential_contDiffAt_chart hb' (g ((A.chart j).symm y)) k hy' (by rw [hsy]; exact b'.mem_U _)
  have c4 := contDiffAt_two_comp_chart_symm_of_smoothOn hZc.isOpen_compl hp' hy' (by rw [hsy]; exact hz')
  have cQ' := fun i => potential_contDiffAt_chart (hQ' i).2 (g ((A.chart j).symm y)) k hy'
    (by rw [hsy]; exact (Q' i).mem_U _)
  have k1 : leviAt A' (th' + LocPot.ofFun ψ' + (b' + LocPot.ofFun p').rsmul t) k
      (A'.chart k (g ((A.chart j).symm y))) (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) =
      ∑ i, s i * levi ((Q' i).φ (g ((A.chart j).symm y)) ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y)))
        (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) +
      levi (ψ' ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y)))
        (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) +
      t * (levi (b'.φ (g ((A.chart j).symm y)) ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y)))
        (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) +
        levi (p' ∘ (A'.chart k).symm) (A'.chart k (g ((A.chart j).symm y)))
        (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w)) := by
    have k2 := hthQ' k _ hy' (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w)
    unfold leviAt at k2 ⊢
    rw [hsy] at k2 ⊢
    rw [← k2]
    exact (levi_add_smul t (c1.add c2) (c3.add c4) _).trans (by rw [levi_add' c1 c2, levi_add' c3 c4])
  rw [k1] at key

  have pb := levi_pull hg hy hk c3 w
  have pp := levi_pull hg hy hk c4 w
  have pψ := levi_pull hg hy hk c2 w
  have pQ := fun i => levi_pull hg hy hk (cQ' i) w

  have gr := fun i => lnRatio_germ pt pt' hA hgpt (hm i) (hm' i) (hQ i).1 (hQ' i).1 hy
  choose G hG hGe using gr
  have cQ : ∀ i, ContDiffAt ℝ 2 (fun v => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm v)) y := fun i =>
    potential_contDiffAt_chart (hQ i).2 ((A.chart j).symm y) j hy ((Q i).mem_U _)
  have cRe : ∀ i, ContDiffAt ℝ 2 (fun v => (G i v).re) y := fun i =>
    (Complex.reCLM.contDiff.contDiffAt.comp y (hG i).restrictScalars.contDiffAt)
  have cL : ∀ i, ContDiffAt ℝ 2 (fun v => lnRatio (m' i) (m i) (pt ((A.chart j).symm v))) y := fun i =>
    ((((cQ i).add (contDiffAt_const.mul (pQ i).1)).add (cRe i))).congr_of_eventuallyEq (hGe i)
  have lL : ∀ i, levi (fun v => lnRatio (m' i) (m i) (pt ((A.chart j).symm v))) y w =
      leviAt A (Q i) j y w - levi ((Q' i).φ (g ((A.chart j).symm y)) ∘ (A'.chart k).symm)
        (A'.chart k (g ((A.chart j).symm y))) (fderiv ℂ (A'.chart k ∘ g ∘ (A.chart j).symm) y w) := fun i => by
    rw [levi_congr (hGe i), levi_add' ((cQ i).add (contDiffAt_const.mul (pQ i).1)) (cRe i),
      levi_add_smul (-1) (cQ i) (pQ i).1, levi_re_analytic (hG i), (pQ i).2]
    simp only [leviAt, Function.comp_def]
    ring

  have hψS : (fun v => ψ ((A.chart j).symm v)) = fun v => ∑ i ∈ Finset.univ, (-s i) *
      lnRatio (m' i) (m i) (pt ((A.chart j).symm v)) + ψ' (g ((A.chart j).symm v)) :=
    funext fun v => by rw [hψ]; ring
  obtain ⟨cψ, lψ⟩ := LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.levi_sum_add Finset.univ (fun i => -s i)
    (fun i v => lnRatio (m' i) (m i) (pt ((A.chart j).symm v))) (fun v => ψ' (g ((A.chart j).symm v))) cL pψ.1 w
  rw [← hψS] at cψ lψ
  have cth : ContDiffAt ℝ 2 (fun v => th.φ ((A.chart j).symm y) ((A.chart j).symm v)) y :=
    potential_contDiffAt_chart hth _ j hy (th.mem_U _)
  have E : leviAt A (th + LocPot.ofFun ψ + (b'.pullback g hg.1 + LocPot.ofFun (p' ∘ g)).rsmul t) j y w =
      leviAt A th j y w + levi (fun v => ψ ((A.chart j).symm v)) y w +
        t * (levi (fun v => b'.φ (g ((A.chart j).symm y)) (g ((A.chart j).symm v))) y w +
          levi (fun v => p' (g ((A.chart j).symm v))) y w) := by
    unfold leviAt
    exact (levi_add_smul t (cth.add cψ) (pb.1.add pp.1) w).trans (by rw [levi_add' cth cψ, levi_add' pb.1 pp.1]; rfl)
  rw [E, pb.2, pp.2, lψ, pψ.2, hthQ j y hy w]
  simp only [lL, mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib] at key ⊢
  linarith

end Main

section Gen

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e e' : ℕ} {X X' : Type} [TopologicalSpace X]
  [TopologicalSpace X'] {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'}

theorem transfer_gen {σ σ' : F →+* ℂ} (hσ : σ' = σ) (pt : X ≃ₜ Pts Y σ) (pt' : X' ≃ₜ Pts Y σ')
    (hA : IsAlgAtlas (tAtlas A pt)) (hA' : IsAlgAtlas (tAtlas A' pt')) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m m' : ∀ i τ, (cxSt F).Met Y τ (Δ i)) (hm : ∀ i τ v, PosAt (m i τ) v) (hm' : ∀ i τ v, PosAt (m' i τ) v)
    (Q : ι → LocPot X) (hQ : ∀ i, IsPot pt (m i σ) (Q i) ∧ IsPotential A (Q i))
    (Q' : ι → LocPot X') (hQ' : ∀ i, IsPot pt' (m' i σ') (Q' i) ∧ IsPotential A' (Q' i)) (s : ι → ℝ)
    (th : LocPot X) (hth : IsPotential A th)
    (hthQ : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A th j y w = ∑ i, s i * leviAt A (Q i) j y w)
    (th' : LocPot X') (hth' : IsPotential A' th')
    (hthQ' : ∀ j, ∀ y ∈ (A'.chart j).target, ∀ w, leviAt A' th' j y w = ∑ i, s i * leviAt A' (Q' i) j y w)
    (Zs : ∀ τ, Set (Pts Y τ)) {Z : Set X} {Z' : Set X'} (hZ : ∀ z, z ∈ Z ↔ pt z ∈ Zs σ)
    (hZ' : ∀ z, z ∈ Z' ↔ pt' z ∈ Zs σ') (hZc : IsClosed Z') (ρ ρ' : ∀ τ, Pts Y τ → ℝ) {r : X → ℝ} {r' : X' → ℝ}
    (hr : ∀ z, z ∉ Z → r z = ρ σ (pt z)) (hr' : ∀ z, z ∉ Z' → r' z = ρ' σ' (pt' z)) {K : ℝ} (hK : 0 < K)
    (hcmp : ∀ v, v ∉ Zs σ → Real.log (ρ' σ v) ≤ K * Real.log (ρ σ v) ∧ Real.log (ρ σ v) ≤ K * Real.log (ρ' σ v))
    (hr1 : ∀ z, z ∉ Z' → 1 ≤ Real.log (r' z)) {b' : LocPot X'} {p' : X' → ℝ} (hpoin : IsPoin A' Z' r' b' p') :
    ∃ (b : LocPot X) (p : X → ℝ), IsPoin A Z r b p ∧ ∀ (mR : ∀ i τ, (cxSt F).Met Y τ (Δ i)) (ψ : X → ℝ) (ψ' : X' → ℝ)
      (t : ℝ), A'.Smooth ψ' → (∀ z, ψ z = ∑ i, (-s i) * lnRatio (mR i σ) (m i σ) (pt z)) →
      (∀ z, ψ' z = ∑ i, (-s i) * lnRatio (mR i σ') (m' i σ') (pt' z)) →
      PshOff A' Z' (th' + LocPot.ofFun ψ' + (b' + LocPot.ofFun p').rsmul t) →
      PshOff A Z (th + LocPot.ofFun ψ + (b + LocPot.ofFun p).rsmul t) := by
  subst σ'
  have hgpt : ∀ z, pt' (pt'.symm (pt z)) = pt z := fun z => pt'.apply_symm_apply _
  have H := hA'.holoMap hA (f := 𝟙 _) (m := id) (fun z => (Category.comp_id _).symm)
  have hg : HoloMap A A' fun z => pt'.symm (pt z) := ⟨(pt.trans pt'.symm).continuous, fun j k => H.2 j k⟩
  have hZZ : ∀ z, z ∈ Z ↔ pt'.symm (pt z) ∈ Z' := fun z => by rw [hZ, hZ', hgpt]
  have hoff : ∀ z, z ∉ Z → pt'.symm (pt z) ∉ Z' ∧ pt z ∉ Zs σ := fun z hz => ⟨(hZZ z).not.1 hz, (hZ z).not.1 hz⟩
  refine ⟨b'.pullback _ hg.1, p' ∘ fun z => pt'.symm (pt z), isPoin_pull hg hZc hZZ hK (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz => hr1 _ (hoff z hz).1) hpoin, fun mR ψ ψ' t hψ' e1 e2 hsh => pshOff_transfer pt pt' hA hg hgpt
    (fun i => m i σ) (fun i => m' i σ) (fun i => hm i σ) (fun i => hm' i σ) Q hQ Q' hQ' s th hth hthQ th' hth' hthQ'
    ψ ψ' hψ' (fun z => ?_) hZc hZZ b' p' hpoin.1 hpoin.2.1 t hsh⟩
  · rw [hr z hz, hr' _ (hoff z hz).1, hgpt]
    exact (hcmp _ (hoff z hz).2).2
  · rw [hr z hz, hr' _ (hoff z hz).1, hgpt]
    exact (hcmp _ (hoff z hz).2).1
  · rw [e1, e2, hgpt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lnRatio]
    ring

end Gen

end GlobalTheory.ArDegIndep.CurvOther

open GlobalTheory.ArDegIndep.CurvOther GlobalTheory.ShFam GlobalTheory.Mean4O.CombForm GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts in

theorem GlobalTheory.ArDegIndep.CurvOther.curv_other : Hypotheses2 → HypothesesH → OnObj fun D O A T H h =>
    ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ (c : O.Y.Comp) (u : Wt O.Y), (∀ τ, StrictAnti (u τ)) →
    ∀ σ : Fin ((T.M c).n + 1), ∃ (b : LocPot ((T.M c).X σ)) (p : (T.M c).X σ → ℝ),
      IsPoin ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) b p ∧ ∃ t : ℝ, ∀ᶠ R in atTop,
        PshOff ((T.M c).A σ) ((T.M c).Z σ)
          ((T.F c).th u σ + LocPot.ofFun (psiOf h x' R u c σ) + (b + LocPot.ofFun p).rsmul t) := by
  intro hP2 hPH D O hO hN A T H h x' c u hu a
  obtain ⟨x, P, hc⟩ := hO
  obtain ⟨P', hB', hc'⟩ := (GlobalTheory.Mean4.exists_setup_core D).1 O x'
  have hO' : (O.withCore x' P' hB').Core := ⟨x', P', hc'⟩
  obtain ⟨A', T', H', ⟨h'⟩⟩ := ReadsEx.exists_reads hP2.p4 hO'
  obtain ⟨b', p', hpoin', C, hC⟩ := GlobalTheory.T.truncated_plurisubharmonic_correction hP2 hPH D _ hO' hN A' T' H' h' c
    ((h'.man c).ε.symm ((h.man c).ε a))
  obtain ⟨K1, hK1, hK1'⟩ := exists_log_r_le x x' (embOf O.κ.e ((h.man c).ε a))
  obtain ⟨K2, hK2, hK2'⟩ := exists_log_r_le x' x (embOf O.κ.e ((h.man c).ε a))
  obtain ⟨Q, hQ, hthQ⟩ := (h.an c).th u a
  obtain ⟨Q', hQ', hthQ'⟩ := (h'.an c).th u ((h'.man c).ε.symm ((h.man c).ε a))
  have hbd := (T'.M c).bd ((h'.man c).ε.symm ((h.man c).ε a))
  have hcmp : ∀ v, v ∉ {v : Pts (O.var c) ((h.man c).ε a) | (O.Φ.C c).π (under v) ∈ genBd O.s.T.Z} →
      Real.log ((O.withCore x' P' hB').met.r c _ v) ≤ max K1 K2 * Real.log (O.met.r c _ v) ∧
        Real.log (O.met.r c _ v) ≤ max K1 K2 * Real.log ((O.withCore x' P' hB').met.r c _ v) := fun v hv => by
    have hv' : ¬ LiesIn ((O.Φ.C c).down v) (genBd O.s.T.Z) := hv
    rw [hc.r_eq]
    exact ⟨(hK1' _ hv').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by
      have := x.exp_le_r (embOf O.κ.e ((h.man c).ε a)) ((O.Φ.C c).down v)
      linarith [Real.add_one_le_exp (1 : ℝ)]))),
      (hK2' _ hv').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by
      have := x'.exp_le_r (embOf O.κ.e ((h.man c).ε a)) ((O.Φ.C c).down v)
      linarith [Real.add_one_le_exp (1 : ℝ)])))⟩
  have hr1 : ∀ z, z ∉ (T'.M c).Z ((h'.man c).ε.symm ((h.man c).ε a)) →
      1 ≤ Real.log ((T'.M c).r ((h'.man c).ε.symm ((h.man c).ε a)) z) := fun z hz => by
    have := hbd.2.2.2.2.2.1 z hz
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) this)).2 this
  obtain ⟨b, p, hpoin, hall⟩ := transfer_gen ((h'.man c).ε.apply_symm_apply _) ((h.man c).pt a)
    ((h'.man c).pt _) (isAlgAtlas_tAtlas (h.man c) a) (isAlgAtlas_tAtlas (h'.man c) _)
    (fun i τ => O.met.h0 c τ (O.ex i)) (fun i τ => (O.withCore x' P' hB').met.h0 c τ (O.ex i))
    (fun i τ v => Setup.Core.referenceMetric_posAt ⟨x, P, hc⟩ c τ _ v) (fun i τ v => hO'.referenceMetric_posAt c τ _ v)
    Q hQ Q' hQ' (fun i => -u i.1 i.2) _ (T.th_pot c u a) hthQ _ (T'.th_pot c u _) hthQ'
    (fun τ => {v | (O.Φ.C c).π (under v) ∈ genBd O.s.T.Z}) ((h.an c).Z a) ((h'.an c).Z _) hbd.1
    (O.met.r c) ((O.withCore x' P' hB').met.r c) (fun z hz => (h.an c).r a z hz) (fun z hz => (h'.an c).r _ z hz)
    (lt_max_of_lt_left hK1) hcmp hr1 hpoin'
  refine ⟨b, p, hpoin, C * ‖u‖, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with R hR
  refine hall (fun i τ => metsOf x' O.Φ c (some R) τ (O.ex i)) _ _ _
    (GlobalTheory.InterpChgSmooth.smooth_phR hP2 hPH D _ hO' hN A' T' H' h' c u _ R hR) (fun z => ?_) (fun z => ?_)
    (hC C le_rfl u R hR fun τ i j hj _ => (hu τ (Fin.lt_def.2 (by omega))).le)
  · simp only [psiOf, chgWith, neg_neg]
  · refine ((h'.an c).phR R hR u _ z).trans ?_
    simp only [Setup.chg, neg_neg]
    try rfl
