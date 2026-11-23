import Development.WeilBound.CoreStatements.CentralCharts.TopLeIffCentre

noncomputable section

namespace AnalyticReference

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB RootFieldNumerics
open scoped ComplexOrder

section Man

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem holoOn_chart (k : Fin A.n) {V : Set (Fin e → ℂ)} {f : (Fin e → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f V) :
    A.HoloOn ((A.chart k).source ∩ A.chart k ⁻¹' V) fun y => f (A.chart k y) := fun j t ht =>
  (hf _ ht.2.2).comp (f := A.chart k ∘ (A.chart j).symm) (A.holo j k t ⟨ht.1, ht.2.1⟩)

theorem periodChart {Ψ : Type} [Finite Ψ] {N j : ℕ} (pot : Ψ × Fin N → LocPot X) (k : Fin A.n) {V : Set (Fin e → ℂ)}
    {gm : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} (hV : IsOpen V) {x : X} (hx : x ∈ (A.chart k).source)
    (hxV : A.chart k x ∈ V) (ha : ∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V) (hd : ∀ t ∈ V, ∀ τ, InFlagDomain N j (gm τ t))
    (hp : ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G (A.chart k x) ∧ ∀ᶠ t in 𝓝 (A.chart k x),
      (pot p).φ x ((A.chart k).symm t) = stepPot N j p.2 (gm p.1 t) + (G t).re) :
    ∃ W, IsPeriodChart A j pot x W fun τ y => gm τ (A.chart k y) := by
  choose G hG hGe using hp
  obtain ⟨V', h', hV', hx'⟩ := eventually_nhds_iff.1 ((hV.eventually_mem hxV).and
    ((Filter.eventually_all.2 fun p => (hG p).eventually_analyticAt).and (Filter.eventually_all.2 hGe)))
  refine ⟨(A.chart k).source ∩ A.chart k ⁻¹' V', (A.chart k).isOpen_inter_preimage hV', ⟨hx, hx'⟩,
    fun τ a b => holoOn_chart A k ((ha τ a b).mono fun t ht => (h' t ht).1), fun τ y hy => hd _ (h' _ hy.2).1 τ,
    fun p => ⟨fun y => G p (A.chart k y), holoOn_chart A k fun t ht => (h' t ht).2.1 p, fun y hy => ?_⟩⟩
  have := (h' _ hy.2).2.2 p
  rwa [(A.chart k).left_inv hy.1] at this

theorem flagImmersion {Ψ : Type} {N : ℕ} (k : Fin A.n) {gm : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {x : X}
    (hx : x ∈ (A.chart k).source) (ha : ∀ τ a b, AnalyticAt ℂ (fun t => gm τ t a b) (A.chart k x))
    (h : ∀ v : Fin e → ℂ, (∀ τ, ((gm τ (A.chart k x))⁻¹ *
      Matrix.of fun a b => fderiv ℂ (fun z => gm τ z a b) (A.chart k x) v).BlockTriangular id) → v = 0) :
    IsFlagImmersionAt A (fun τ y => gm τ (A.chart k y)) x := by
  intro k' hx' v hv
  let T := A.chart k ∘ (A.chart k').symm
  let T' := A.chart k' ∘ (A.chart k).symm
  have e₁ : T (A.chart k' x) = A.chart k x := congrArg _ ((A.chart k').left_inv hx')
  have hT : DifferentiableAt ℂ T (A.chart k' x) :=
    (A.holo k' k _ ⟨(A.chart k').map_source hx', by
      rw [Set.mem_preimage]; rwa [(A.chart k').left_inv hx']⟩).differentiableAt
  have hT' : DifferentiableAt ℂ T' (T (A.chart k' x)) := by
    rw [e₁]
    exact (A.holo k k' _ ⟨(A.chart k).map_source hx, by
      rw [Set.mem_preimage]; rwa [(A.chart k).left_inv hx]⟩).differentiableAt
  have h0 : fderiv ℂ T (A.chart k' x) v = 0 := h _ fun τ => by
    have e₂ : (Matrix.of fun a b => fderiv ℂ (fun z => gm τ z a b) (A.chart k x) (fderiv ℂ T (A.chart k' x) v)) =
        Matrix.of fun a b => fderiv ℂ (fun z => gm τ (A.chart k ((A.chart k').symm z)) a b) (A.chart k' x) v := by
      ext a b
      have h1 : DifferentiableAt ℂ (fun t => gm τ t a b) (T (A.chart k' x)) := by
        rw [e₁]
        exact (ha τ a b).differentiableAt
      have h2 := fderiv_comp _ h1 hT
      rw [e₁] at h2
      exact (congrArg (fun L : (Fin e → ℂ) →L[ℂ] ℂ => L v) h2).symm
    rw [e₂]
    exact hv τ
  have hid : T' ∘ T =ᶠ[𝓝 (A.chart k' x)] id := by
    have hc : ContinuousAt (A.chart k').symm (A.chart k' x) := (A.chart k').continuousAt_symm ((A.chart k').map_source hx')
    have h1 : ∀ᶠ t in 𝓝 (A.chart k' x), (A.chart k').symm t ∈ (A.chart k).source :=
      hc.eventually_mem ((A.chart k).open_source.mem_nhds (by rwa [(A.chart k').left_inv hx']))
    filter_upwards [h1, (A.chart k').open_target.mem_nhds ((A.chart k').map_source hx')] with t h1 h2
    show A.chart k' ((A.chart k).symm (A.chart k ((A.chart k').symm t))) = t
    rw [(A.chart k).left_inv h1, (A.chart k').right_inv h2]
  have h3 := hid.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp _ hT' hT, fderiv_id] at h3
  have h4 := congrArg (fun L => L v) h3
  simpa [h0] using h4.symm

end Man

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

theorem unif_of (hLP : LocPer) (hT : Transport) (hFV : FrameVals) (hPM : PerMat) (hFI : FlagImm) (hC : CountGen)
    (hG : Top.Given) (hN : 1 ≤ D.p + D.q) (Gr : RefGeo Y) (An : Gr.An) :
    IsUniformised An.Sys.A An.Sys.open' D.p fun p => An.Sys.potH (some p) := by
  obtain ⟨ψ, hψ, hπ, hπ'⟩ := exists_inv An.Sys.A An.Re.R.A An.Re.π An.Re.br An.Re.holo (An.deg_one ▸ An.Re.degree) An.π_bij
  obtain ⟨z, hzi, hzc, hzh, hzU⟩ := ptsFam Gr An ψ hψ hπ hπ'
  constructor
  · intro x hx
    obtain ⟨k, hk⟩ := An.Sys.A.cover x
    obtain ⟨V, gm, hV, hxV, -, -, ha, hfd, hp, -⟩ :=
      locChart hLP hT hFV hPM hG hN Gr An ψ hψ hπ z hzi hzc k (hzh k) ⊤ x hx hk trivial
    obtain ⟨W, hW⟩ := periodChart An.Sys.A (fun p => An.Sys.potH (some p)) k hV hk hxV ha hfd fun p => by
      have := hp _ hxV p
      rwa [(An.Sys.A.chart k).left_inv hk] at this
    exact ⟨W, _, hW⟩
  · obtain ⟨U, hU, hcnt⟩ := hC hG E H D l Xo c Y Gr.Ω Gr.K Gr.J Gr.y Gr.𝔐 Gr.Fl hN Gr.deg_one
    obtain ⟨x, hx, hxU⟩ := hzU U hU
    obtain ⟨k, hk⟩ := An.Sys.A.cover x
    obtain ⟨V, gm, hV, hxV, hVt, hVo, ha, hfd, hp, hcV⟩ :=
      locChart hLP hT hFV hPM hG hN Gr An ψ hψ hπ z hzi hzc k (hzh k) U x hx hk hxU
    obtain ⟨t, ht, him⟩ := hFI (CMType H) _ _ V gm hV ⟨_, hxV⟩ ha (fun t ht τ => (hfd t ht τ).1) (hcV hcnt)
    have e : An.Sys.A.chart k ((An.Sys.A.chart k).symm t) = t := (An.Sys.A.chart k).right_inv (hVt ht)
    have hs := (An.Sys.A.chart k).map_target (hVt ht)
    obtain ⟨W, hW⟩ := periodChart An.Sys.A (fun p => An.Sys.potH (some p)) k hV hs (by rwa [e]) ha hfd fun p => by
      rw [e]
      exact hp t ht p
    exact ⟨_, hVo t ht, W, _, hW, flagImmersion An.Sys.A k hs (fun τ a b => by rw [e]; exact ha τ a b t ht) (by rwa [e])⟩

end AnalyticReference
