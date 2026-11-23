import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pot

theorem log_norm_an {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀)
    (h0 : F t₀ ≠ 0) : ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, Real.log ‖F t‖ = (G t).re := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have e1 : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
  refine ⟨fun t => Complex.log (F t / F t₀) + (Real.log ‖F t₀‖ : ℂ), (hH.clog e1).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem val_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) {a : Ω} {r : ℂ} (h : ValAt ξ (z t₀) a r) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u t₀ ∧ ∀ᶠ t in 𝓝 t₀, ValAt ξ (z t) a (u t) := by
  obtain ⟨h0, s, rfl, -⟩ := h
  obtain ⟨U, hU, f, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : centre ξ ∈ U := h0.mem_open U.isOpen hU
  have hn : {b ∈ B | ⊤ ≤ z b ⁻¹ᵁ U} ∈ 𝓝 t₀ := (hz U f).1.mem_nhds ⟨ht, (SheetDecomposition.CovSch.top_le_iff _ _).2 hU⟩
  refine ⟨fun b => valAt' (z b) U f, GlobalTheory.SCV.analyticAt_of_differentiableOn (hz U f).2 hn, ?_⟩
  filter_upwards [hn] with t h1
  have h2 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h1.2
  rw [SheetDecomposition.CovSch.valAt'_eq _ _ h2, SheetDecomposition.CovSch.genMap_germ' ⟨centre (z t₀), h0⟩ U hU hg f]
  exact SheetDecomposition.CovSch.valAt_sec (hall _) U h2 hg f

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem coords_orbit {z : Sp ℂ ⟶ X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w') (hs : SameOrbit w w') :
    CoordsAt ξ y z w := by
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨fun k => (h.1 k).imp fun i hi => (IsUnit.mk0 _ (ha k)).mul hi, fun k i hi => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k i (isUnit_of_mul_isUnit_right hi)
  refine ⟨h1, fun j => (h2 j).imp fun r hr => ⟨hr.1, ?_⟩⟩
  show a k * w' ⟨k, j⟩ = r * (a k * w' ⟨k, i⟩)
  rw [hr.2]
  ring

theorem log_h_smul (A : HermLine J) (a : K → ℂ) (ha : ∀ k, a k ≠ 0) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => a p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖a k‖ + Real.log (A.h w) := by
  have h1 : ∀ k, ‖a k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (ha k))
  rw [A.smul a w ha, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => h1 k) (A.pos w hw).ne',
    Real.log_prod fun k _ => h1 k]
  simp only [Real.log_zpow]

theorem log_orbit {I : Type} (s : Finset I) (A : HermLine J) (B : I → HermLine J) (hd : A.a = -∑ i ∈ s, (B i).a)
    {w w' : (Σ k, J k) → ℂ} (hs : SameOrbit w w') (hw : ∀ k, ∃ i, w' ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ i ∈ s, Real.log ((B i).h w) = Real.log (A.h w') + ∑ i ∈ s, Real.log ((B i).h w') := by
  obtain ⟨a, ha, rfl⟩ := hs
  simp only [log_h_smul _ a ha hw, hd, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem log_h_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) (A : HermLine J) (e₀ T : Ω)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : ∀ p, AnalyticAt ℂ (fun t => γ t p) t₀) {ν : (Fin n → ℂ) → ℝ}
    (hν : ∀ᶠ t in 𝓝 t₀, 0 < ν t ∧ SecNorm ξ y A e₀ (z t) (γ t) T (ν t)) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, -Real.log (A.h (γ t)) = Real.log (ν t) + (G t).re := by
  obtain ⟨p0, h0⟩ := hν.self_of_nhds
  obtain ⟨c, hc⟩ := h0.exists_chart
  obtain ⟨u₀, hu₀, e0⟩ := h0.2.2 c hc
  obtain ⟨u, hu, hue⟩ := val_an hz hall ht hu₀
  let F : (Fin n → ℂ) → ℂ := fun t => u t * ∏ k, γ t ⟨k, c k⟩ ^ A.a k
  have hF : AnalyticAt ℂ F t₀ := hu.mul (Finset.analyticAt_fun_prod _ fun k _ => (hγ _).zpow (hc k))
  have hcn : ∀ᶠ t in 𝓝 t₀, ∀ k, γ t ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hγ _).continuousAt.eventually_ne (hc k)
  have hev : ∀ᶠ t in 𝓝 t₀, ν t * A.h (γ t) = ‖F t‖ := by
    filter_upwards [hν, hue, hcn] with t h1 h2 h3
    obtain ⟨u', hu', e⟩ := h1.2.2.2 c h3
    rw [e, CxVal.unique hu' h2]
    simp only [F, norm_mul, norm_prod, norm_zpow]
  have hF0 : F t₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hev.self_of_nhds]
    exact (mul_pos p0 (A.pos _ fun k => ⟨c k, hc k⟩)).ne'
  obtain ⟨G, hG, hGe⟩ := log_norm_an hF hF0
  refine ⟨fun t => -G t, hG.neg, ?_⟩
  filter_upwards [hν, hev, hcn, hGe] with t h1 h2 h3 h4
  rw [Complex.neg_re, ← h4, ← h2, Real.log_mul h1.1.ne' (A.pos _ fun k => ⟨c k, h3 k⟩).ne']
  ring

theorem holo_comp {e e' : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {A : FinHolAtlas e M}
    {B : FinHolAtlas e' N} {ψ : M → N} (hψ : HoloMap A B ψ) (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target)
    {W : Set N} {f : N → ℂ} (hf : B.HoloOn W f) (hW : ψ ((A.chart k).symm t) ∈ W) :
    AnalyticAt ℂ (fun t' => f (ψ ((A.chart k).symm t'))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 := hψ.2 k j t ⟨ht, hj⟩
  have h2 := hf j (B.chart j (ψ ((A.chart k).symm t))) ⟨(B.chart j).map_source hj, by
    show (B.chart j).symm _ ∈ W
    rwa [(B.chart j).left_inv hj]⟩
  have h3 := AnalyticAt.comp (f := B.chart j ∘ ψ ∘ (A.chart k).symm) (x := t) h2 h1
  refine h3.congr ?_
  have hc : ContinuousAt (fun t' => ψ ((A.chart k).symm t')) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually_mem ((B.chart j).open_source.mem_nhds hj)] with t' h
  simp only [Function.comp_apply, (B.chart j).left_inv h]

end Pot

open Pot in
theorem potLoc : PotLoc := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ k V z tr ν hψ hπ hV hVt hpt t₁ ht₁ p
  classical
  obtain ⟨τ, i⟩ := p
  let w : _ → Or.Re.R.X := fun t => ψ ((Sys.A.chart k).symm t)
  let γ : _ → (Σ k, RM.ι k) → ℂ := fun t => Or.Re.R.lift (w t₁) (w t)
  have hwc : ∀ t ∈ V, ContinuousAt w t := fun t ht =>
    hψ.1.continuousAt.comp ((Sys.A.chart k).continuousAt_symm (hVt ht))
  let B := V ∩ w ⁻¹' Or.Re.R.U (w t₁)
  have hB : IsOpen B := (continuousOn_of_forall_continuousAt hwc).isOpen_inter_preimage hV (Or.Re.R.isOpen_U _)
  have ht₁B : t₁ ∈ B := ⟨ht₁, Or.Re.R.mem_U _⟩
  have hγ : ∀ t ∈ B, ∀ q, AnalyticAt ℂ (fun t => γ t q) t := fun t ht q =>
    holo_comp hψ k (hVt ht.1) (Or.Re.R.holo (w t₁) q) ht.2
  have horb : ∀ t ∈ B, SameOrbit (γ t) (Or.Re.R.lift (w t) (w t)) := fun t ht => Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩
  have hco : ∀ t ∈ B, CoordsAt Or.𝔐.ξ RM.y (z t) (γ t) := fun t ht => coords_orbit (hpt t ht.1).2.1 (horb t ht)
  have hz : IsHolTo B z := GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ B γ z hB
    (differentiableOn_pi.2 fun q t ht => (hγ t ht q).differentiableAt.differentiableWithinAt) hco
  have hop : ∀ t ∈ V, Or.Re.π (w t) ∈ Sys.open' := fun t ht => by
    rw [hπ]
    exact (hpt t ht).1
  have hin : ∀ t ∈ V, Or.𝔐.Interior (z t) := fun t ht => (Or.interior (w t) (z t) (hpt t ht).2.1).2 (hop t ht)
  have hroot : ∀ r : RootIx D, ∃ G : _ → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      -Real.log ((Or.sing r).h (γ t)) = Real.log (ν r t ^ HodgeCpt.rootSgn D r) + (G t).re := fun r => by
    refine log_h_an (y := RM.y) hz Or.𝔐.all ht₁B (Or.sing r) (Or.e r) (tr r ^ HodgeCpt.rootSgn D r) (hγ t₁ ht₁B) ?_
    filter_upwards [hB.mem_nhds ht₁B] with t ht
    exact ⟨zpow_pos ((hpt t ht.1).2.2 r).pos _, Or.hodge r (z t) (γ t) (hco t ht) (hin t ht.1) _ _ ((hpt t ht.1).2.2 r)⟩
  choose G hG hGe using hroot
  obtain ⟨W, hW, hwW, G₀, hG₀, e₀⟩ := Or.Re.ref_pot (some (τ, i)) (w t₁) trivial
  have hG₀a : AnalyticAt ℂ (fun t => G₀ (w t)) t₁ := holo_comp hψ k (hVt ht₁) hG₀ hwW
  refine ⟨fun t => ∑ j ∈ Finset.Iic i, G (τ, j) t - G₀ (w t),
    (Finset.analyticAt_fun_sum _ fun j _ => hG _).sub hG₀a, ?_⟩
  filter_upwards [hB.mem_nhds ht₁B, (hwc t₁ ht₁).eventually_mem (hW.mem_nhds hwW),
    (Filter.eventually_all_finset (Finset.Iic i)).2 fun j _ => hGe (τ, j)] with t ht htW h3
  have e1 : Real.log ((Or.Re.ref (some (τ, i))).h (γ t)) -
      (Sys.th (some (τ, i))).φ (Or.Re.π (w t₁)) (Or.Re.π (w t)) = (G₀ (w t)).re := e₀ (w t) htW
  have e2 := Or.fund_sing τ i (w t) (hop t ht.1)
  have e3 := log_orbit (Finset.Iic i) (Or.Re.ref (some (τ, i))) (fun j => Or.sing (τ, j))
    (by rw [Or.fund_deg]; simp only [Or.sing_deg]) (horb t ht) (Or.Re.R.mem _ _ (Or.Re.R.mem_U _)).1
  have e4 : ∑ j ∈ Finset.Iic i, -Real.log ((Or.sing (τ, j)).h (γ t)) =
      ∑ j ∈ Finset.Iic i, ((HodgeCpt.rootSgn D (τ, j) : ℝ) * Real.log (ν (τ, j) t) + (G (τ, j) t).re) :=
    Finset.sum_congr rfl fun j hj => by rw [h3 j hj, Real.log_zpow]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at e4
  simp only [w, hπ] at e1 e2
  show (Sys.th (some (τ, i))).φ _ _ + Sys.ph (some (τ, i)) _ = _
  rw [Complex.sub_re, Complex.re_sum]
  simp only [w] at e3 ⊢
  linarith

end RootFieldNumerics
