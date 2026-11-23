import Development.WeilBound.CoreStatements.FlagImmersions.ContAtOfHoloOn
import Development.WeilBound.CoreStatements.FlagImmersions.CoordsOrbit
import Development.WeilBound.CoreStatements.FlagImmersions.IsHolToOfLocal
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric

noncomputable section

namespace AnalyticReference

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB RootFieldNumerics
open scoped ComplexOrder

theorem exists_inv {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (S : Set X) (hh : HoloMap B A h)
    (hd : IsDegreeOff A B h 1 S) (hb : Function.Bijective h) :
    ∃ ψ : X → Y, HoloMap A B ψ ∧ (∀ x, h (ψ x) = x) ∧ ∀ w, ψ (h w) = w := by
  let φ : Y ≃ₜ X := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h hb) hh.1
  have h1 : ∀ x, h (φ.symm x) = x := φ.apply_symm_apply
  have h2 : ∀ w, φ.symm (h w) = w := φ.symm_apply_apply
  refine ⟨φ.symm, ⟨φ.symm.continuous, fun j k => ?_⟩, h1, h2⟩
  have hU : IsOpen (φ.symm ⁻¹' (B.chart k).source) := (B.chart k).open_source.preimage φ.symm.continuous
  intro t ht
  refine analyticAt_pi_iff.2 fun i => ?_
  obtain ⟨F, hF, hFf⟩ := descend e X Y A B h S _ (fun y => B.chart k y i) hh hd hU fun j' u hu => by
    have hs : (B.chart j').symm u ∈ (B.chart k).source := by
      have := hu.2
      rwa [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, h2] at this
    exact analyticAt_pi_iff.1 (B.holo j' k u ⟨hu.1, hs⟩) i
  refine (hF j t ht).congr ?_
  filter_upwards [((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ht] with u hu
  have := hFf (φ.symm ((A.chart j).symm u)) (by rw [h1]; exact hu.2)
  rw [h1] at this
  exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

open Pot in
theorem potLoc (Gr : RefGeo Y) (An : Gr.An)
    (ψ : An.Sys.X → An.Re.R.X) (k : Fin An.Sys.A.n) (V : Set (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ))
    (z : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → (Sp ℂ ⟶ Gr.𝔐.X)) (tr : RootIx D → Gr.Ω)
    (ν : RootIx D → (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℝ) :
    HoloMap An.Sys.A An.Re.R.A ψ → (∀ x, An.Re.π (ψ x) = x) → IsOpen V → V ⊆ (An.Sys.A.chart k).target →
    (∀ t ∈ V, (An.Sys.A.chart k).symm t ∈ An.Sys.open' ∧
      CoordsAt Gr.𝔐.ξ Gr.y (z t) (An.Re.R.lift (ψ ((An.Sys.A.chart k).symm t)) (ψ ((An.Sys.A.chart k).symm t))) ∧
      ∀ r, Gr.𝔐.M.IsGrNorm Gr.𝔐.t.PP.L (Gr.𝔐.V (HodgeCpt.rootIdx D r).1) (Gr.Fl.b (HodgeCpt.rootIdx D r).1)
        (HodgeCpt.rootIdx D r).2 (z t) (tr r) (ν r t)) →
    ∀ t₁ ∈ V, ∀ p : RootIx D, ∃ G : (Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ) → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      (An.Sys.potH (some p)).φ ((An.Sys.A.chart k).symm t₁) ((An.Sys.A.chart k).symm t) =
        ∑ i ∈ Finset.Iic p.2, (HodgeCpt.rootSgn D (p.1, i) : ℝ) * Real.log (ν (p.1, i) t) + (G t).re := by
  intro hψ hπ hV hVt hpt t₁ ht₁ p
  classical
  obtain ⟨τ, i⟩ := p
  let w : _ → An.Re.R.X := fun t => ψ ((An.Sys.A.chart k).symm t)
  let γ : _ → (Σ k, Gr.J k) → ℂ := fun t => An.Re.R.lift (w t₁) (w t)
  have hwc : ∀ t ∈ V, ContinuousAt w t := fun t ht =>
    hψ.1.continuousAt.comp ((An.Sys.A.chart k).continuousAt_symm (hVt ht))
  let B := V ∩ w ⁻¹' An.Re.R.U (w t₁)
  have hB : IsOpen B := (continuousOn_of_forall_continuousAt hwc).isOpen_inter_preimage hV (An.Re.R.isOpen_U _)
  have ht₁B : t₁ ∈ B := ⟨ht₁, An.Re.R.mem_U _⟩
  have hγ : ∀ t ∈ B, ∀ q, AnalyticAt ℂ (fun t => γ t q) t := fun t ht q =>
    holo_comp hψ k (hVt ht.1) (An.Re.R.holo (w t₁) q) ht.2
  have horb : ∀ t ∈ B, SameOrbit (γ t) (An.Re.R.lift (w t) (w t)) := fun t ht => An.Re.R.compat _ _ _ ⟨ht.2, An.Re.R.mem_U _⟩
  have hco : ∀ t ∈ B, CoordsAt Gr.𝔐.ξ Gr.y (z t) (γ t) := fun t ht => coords_orbit (hpt t ht.1).2.1 (horb t ht)
  have hz : IsHolTo B z := GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Gr.𝔐.ξ _ _ Gr.y Gr.𝔐.tie Gr.𝔐.all _ B γ z hB
    (differentiableOn_pi.2 fun q t ht => (hγ t ht q).differentiableAt.differentiableWithinAt) hco
  have hop : ∀ t ∈ V, An.Re.π (w t) ∈ An.Sys.open' := fun t ht => by
    rw [hπ]
    exact (hpt t ht).1
  have hin : ∀ t ∈ V, Gr.𝔐.Interior (z t) := fun t ht => (An.interior (w t) (z t) (hpt t ht).2.1).2 (hop t ht)
  have hroot : ∀ r : RootIx D, ∃ G : _ → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      -Real.log ((An.sing r).h (γ t)) = Real.log (ν r t ^ HodgeCpt.rootSgn D r) + (G t).re := fun r => by
    refine log_h_an (y := Gr.y) hz Gr.𝔐.all ht₁B (An.sing r) (Gr.e r) (tr r ^ HodgeCpt.rootSgn D r) (hγ t₁ ht₁B) ?_
    filter_upwards [hB.mem_nhds ht₁B] with t ht
    exact ⟨zpow_pos ((hpt t ht.1).2.2 r).pos _, An.hodge r (z t) (γ t) (hco t ht) (hin t ht.1) _ _ ((hpt t ht.1).2.2 r)⟩
  choose G hG hGe using hroot
  obtain ⟨W, hW, hwW, G₀, hG₀, e₀⟩ := An.Re.ref_pot (some (τ, i)) (w t₁) trivial
  have hG₀a : AnalyticAt ℂ (fun t => G₀ (w t)) t₁ := holo_comp hψ k (hVt ht₁) hG₀ hwW
  refine ⟨fun t => ∑ j ∈ Finset.Iic i, G (τ, j) t - G₀ (w t),
    (Finset.analyticAt_fun_sum _ fun j _ => hG _).sub hG₀a, ?_⟩
  filter_upwards [hB.mem_nhds ht₁B, (hwc t₁ ht₁).eventually_mem (hW.mem_nhds hwW),
    (Filter.eventually_all_finset (Finset.Iic i)).2 fun j _ => hGe (τ, j)] with t ht htW h3
  have e1 : Real.log ((An.Re.ref (some (τ, i))).h (γ t)) -
      (An.Sys.th (some (τ, i))).φ (An.Re.π (w t₁)) (An.Re.π (w t)) = (G₀ (w t)).re := e₀ (w t) htW
  have e2 := An.fund_sing τ i (w t) (hop t ht.1)
  have e3 := log_orbit (Finset.Iic i) (An.Re.ref (some (τ, i))) (fun j => An.sing (τ, j))
    (by rw [An.fund_deg]; simp only [An.sing_deg]) (horb t ht) (An.Re.R.mem _ _ (An.Re.R.mem_U _)).1
  have e4 : ∑ j ∈ Finset.Iic i, -Real.log ((An.sing (τ, j)).h (γ t)) =
      ∑ j ∈ Finset.Iic i, ((HodgeCpt.rootSgn D (τ, j) : ℝ) * Real.log (ν (τ, j) t) + (G (τ, j) t).re) :=
    Finset.sum_congr rfl fun j hj => by rw [h3 j hj, Real.log_zpow]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at e4
  simp only [w, hπ] at e1 e2
  show (An.Sys.th (some (τ, i))).φ _ _ + An.Sys.ph (some (τ, i)) _ = _
  rw [Complex.sub_re, Complex.re_sum]
  simp only [w] at e3 ⊢
  linarith

open Pts in
theorem ptsFam (Gr : RefGeo Y) (An : Gr.An) (ψ : An.Sys.X → An.Re.R.X) (hψ : HoloMap An.Sys.A An.Re.R.A ψ)
    (hπψ : ∀ x, An.Re.π (ψ x) = x) (hψπ : ∀ w, ψ (An.Re.π w) = w) :
    ∃ z : An.Sys.X → (Sp ℂ ⟶ Gr.𝔐.X), Function.Injective z ∧ (∀ x, CoordsAt Gr.𝔐.ξ Gr.y (z x) (An.Re.R.lift (ψ x) (ψ x))) ∧
      (∀ k, IsHolTo (An.Sys.A.chart k).target fun t => z ((An.Sys.A.chart k).symm t)) ∧
      ∀ U : Gr.𝔐.X.Opens, genPt Gr.𝔐.ξ ∈ U → ∃ x ∈ An.Sys.open', centre (z x) ∈ U := by
  have hnJ : ∀ w, w ∉ mcPts An.Re.J := fun w => by rw [An.J_top]; exact not_mem_top w
  choose z hz using fun x : An.Sys.X =>
    SheetDecomposition.exists_pt Gr.𝔐 (An.Re.R.mem (ψ x) (ψ x) (An.Re.R.mem_U (ψ x)))
  have hol : ∀ k, IsHolTo (An.Sys.A.chart k).target fun t => z ((An.Sys.A.chart k).symm t) := fun k => by
    refine isHolTo_of_local fun t₀ ht₀ => ?_
    let w₀ := ψ ((An.Sys.A.chart k).symm t₀)
    have hB : IsOpen ((An.Sys.A.chart k).target ∩ (An.Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' An.Re.R.U w₀)) :=
      (An.Sys.A.chart k).symm.isOpen_inter_preimage ((An.Re.R.isOpen_U w₀).preimage hψ.1)
    refine ⟨(An.Sys.A.chart k).target ∩ (An.Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' An.Re.R.U w₀), Set.inter_subset_left,
      ⟨ht₀, An.Re.R.mem_U w₀⟩, ?_⟩
    refine GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Gr.𝔐.ξ _ _ Gr.y Gr.𝔐.tie Gr.𝔐.all _ _
      (fun t => An.Re.R.lift w₀ (ψ ((An.Sys.A.chart k).symm t))) _ hB ?_ ?_
    · refine differentiableOn_pi.2 fun p t ht => ?_
      exact (analyticAt_comp hψ (An.Re.R.holo w₀ p) k ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      exact SheetDecomposition.coords_of_sat Gr.𝔐 (hz _) (sat_iff.2 (An.Re.R.compat _ _ _ ⟨ht.2, An.Re.R.mem_U _⟩))
  refine ⟨z, fun x x' e => ?_, hz, hol, fun U hU => ?_⟩
  · have h := sat_iff.1 (SheetDecomposition.sat_of_coords Gr.𝔐 (hz x') (e ▸ hz x))
    rw [← hπψ x, An.Re.R.inj _ _ (hnJ _) h, hπψ]
  · obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form Gr.𝔐.tie U hU
    obtain ⟨w, hw, hwg⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts (J := Ideal.span {g}) An.Re.arith
      (fun h => hg (h (Ideal.subset_span rfl)))
    have hg0 : MvPolynomial.aeval w g ≠ 0 := fun h0 => hwg ⟨hw.1, fun f hf => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
      have : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
        rw [MvPolynomial.eval_map]
        exact h0
      rw [map_mul, map_mul, this, mul_zero]⟩
    obtain ⟨w₁, hw₁⟩ := An.Re.R.surj w hw (hnJ w)
    have hsym : SameOrbit w (An.Re.R.lift w₁ w₁) := by
      obtain ⟨a, ha, h⟩ := hw₁
      refine ⟨fun k => (a k)⁻¹, fun k => inv_ne_zero (ha k), funext fun p => ?_⟩
      rw [h]
      simp only [inv_mul_cancel_left₀ (ha _)]
    have hc : CoordsAt Gr.𝔐.ξ Gr.y (z (An.Re.π w₁)) w :=
      SheetDecomposition.coords_of_sat Gr.𝔐 (hz _) (sat_iff.2 (by rw [hψπ]; exact hsym))
    have hx₀ : centre (z (An.Re.π w₁)) ∈ U := hgU _ _ (Gr.𝔐.all _) hc hg0
    obtain ⟨k, hk⟩ := An.Sys.A.cover (An.Re.π w₁)
    have hopen := (An.Sys.A.chart k).isOpen_inter_preimage (hol k U 0).1
    have hd := (GlobalTheory.T.section_boundary_closed_and_codense _ _ An.Sys.A An.Sys.L An.Sys.s An.Sys.nb An.Sys.m An.Sys.W An.Sys.sec An.Sys.snc).2
    obtain ⟨x, ⟨hxs, -, hxU⟩, hxo⟩ := hd.inter_open_nonempty _ hopen ⟨An.Re.π w₁, hk, (An.Sys.A.chart k).map_source hk, by
      show ⊤ ≤ z ((An.Sys.A.chart k).symm (An.Sys.A.chart k _)) ⁻¹ᵁ U
      rw [(An.Sys.A.chart k).left_inv hk]
      exact (SheetDecomposition.top_le_iff_pt _ _ _).2 hx₀⟩
    refine ⟨x, hxo, ?_⟩
    have h2 : ⊤ ≤ z ((An.Sys.A.chart k).symm (An.Sys.A.chart k x)) ⁻¹ᵁ U := hxU
    rw [(An.Sys.A.chart k).left_inv hxs] at h2
    exact (SheetDecomposition.top_le_iff_pt _ _ _).1 h2

end AnalyticReference
