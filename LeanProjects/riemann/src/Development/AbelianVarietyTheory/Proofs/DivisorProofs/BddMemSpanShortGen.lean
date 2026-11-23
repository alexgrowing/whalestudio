import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SupFull

theorem isBddSec_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (t : ℂ) (h : X.IsBddSec la P) : X.IsBddSec la (t • P) := by
  obtain ⟨⟨h1, h2, h3⟩, C, hC⟩ := h
  refine ⟨⟨h1.const_smul t, fun x hx b hb => ?_, fun g hg x hx => ?_⟩, ‖t‖ * C, fun x hx => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, h2 x hx b hb]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, h3 g hg x hx]; ring
  · rw [Formalism.L2.PjFree.pnorm_smul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)

set_option maxHeartbeats 800000 in

theorem bdd_mem_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → ∀ P : Formalism.L2.PjFree.FDSec U.X, (∀ k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a n k) (P k)) → (∀ k x, x ∉ (U.X k).dom → P k x = 0) → P ∈ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hpr hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hchi htot P hP1 hP0
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => GlobalTheory.T.isStabiliserInvariant_pull_bounded_section E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_smul _ (hP1 k))
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2, -⟩ := ((hpull k).2 0 (differentiableOn_const 0) (by simp)).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_datum_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ∃ (d : DeltaDat Xo c n) (nab : NabV Xo c), d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1) ∧ d.l₂ = l ∧ (∃ ph ψ x₀, d.PhiPin ph ψ x₀) ∧ ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a n k) (Formalism.L2.PjFree.rdU U f k)) → f ∈ Submodule.span c.F (shortGen Xo c nab 1 0 a n d) := by
  intro E _ _ _ H Dw l Xo c r σ U hr hA hσ hU hG hP a n hdom hn hχ
  have hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.ChartFree.chartIndep
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂ = l ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hle, ph, x₀, hpin⟩ := hd
  have hAe : d.l₂.A = l.A := congrArg (·.A) hle
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine ⟨d, nab, hlev, hnab, fun k _ _ y => ?_, hle, ⟨ph, 1, x₀, hpin⟩, fun f hf hb => ?_⟩
  · rw [pow_one, hδ]
    exact evalAt_one _ _ _ (hT _ _)
  · exact mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU U) (sec Xo c a n)
      (GlobalTheory.reading_linearIndependent_and_injective hB E H Dw l Xo c σ r U hU a n).1 _ (fun g hg => hg.1) hf
      (bdd_mem_span_shortGen hC E H Dw l Xo c n d σ r U hσ hU hr hA hG hP hlev hnab hunit h3
        (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot _ hb fun k x hx => dif_neg hx)

end GlobalTheory.SupFull
