import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ClopenPush

section General

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D : ℕ} {u : CxPts q σ' → CxPts p σ}

theorem contDiffAt_chart_of_lifts (hu : IsOpenEmbedding u)
    (hL : ∀ (W : Y.Opens) (g : Γ(Y, W)) (y : CxPts q σ'), y ∈ ptsIn q σ' W →
      ∃ (V : X.Opens) (G : Γ(X, V)), u y ∈ ptsIn p σ V ∧
        ∀ y' : CxPts q σ', u y' ∈ ptsIn p σ V → y' ∈ ptsIn q σ' W ∧ ev p σ V G (u y') = ev q σ' W g y')
    {f : CxPts p σ → ℝ} {y : CxPts q σ'} (h : CInfAt (f ∘ u) y) (c : AlgChart p σ D)
    {v : V D} (hv : v ∈ c.e.target) (hy : c.e.symm v = u y) :
    ContDiffAt ℝ ∞ (f ∘ c.e.symm) v := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  choose V G hV hG using fun a => hL W (g a) y h₁
  have hg : ContDiffAt ℝ ∞ (fun w a => ev p σ (V a) (G a) (c.e.symm w)) v := contDiffAt_pi.2 fun a => by
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (V a))
    exact (ChartGlue.contDiffOn_real ho (c.holo (V a) (G a))).contDiffAt
      (ho.mem_nhds ⟨hv, by rw [Set.mem_preimage, hy]; exact hV a⟩)
  have hpt : (fun a => ev p σ (V a) (G a) (c.e.symm v)) = fun a => ev q σ' W (g a) y :=
    funext fun a => by rw [hy]; exact (hG a y (hV a)).2
  have hF : ContDiffAt ℝ ∞ F (fun a => ev p σ (V a) (G a) (c.e.symm v)) := by
    rw [hpt]
    exact h₄.contDiffAt (h₂.mem_nhds h₃)
  have hev : f =ᶠ[𝓝 (c.e.symm v)] fun z => F fun a => ev p σ (V a) (G a) z := by
    rw [hy, ← hu.map_nhds_eq]
    have hall : ∀ᶠ y' in 𝓝 y, ∀ a, u y' ∈ ptsIn p σ (V a) :=
      eventually_all.2 fun a =>
        hu.continuous.continuousAt.eventually ((isOpen_ptsIn (V a)).mem_nhds (hV a))
    change ∀ᶠ y' in 𝓝 y, f (u y') = F fun a => ev p σ (V a) (G a) (u y')
    filter_upwards [h₅, hall] with y' e hy'
    rw [show (fun a => ev p σ (V a) (G a) (u y')) = fun a => ev q σ' W (g a) y' from
      funext fun a => (hG a y' (hy' a)).2]
    exact e
  exact (hF.comp v hg).congr_of_eventuallyEq ((c.e.continuousAt_symm hv).eventually hev)

theorem isPotential_pot_of_lifts [CompactSpace (CxPts p σ)] (R : AnRead p σ D)
    (hu : IsOpenEmbedding u) (hc : IsClosed (Set.range u))
    (hL : ∀ (W : Y.Opens) (g : Γ(Y, W)) (y : CxPts q σ'), y ∈ ptsIn q σ' W →
      ∃ (V : X.Opens) (G : Γ(X, V)), u y ∈ ptsIn p σ V ∧
        ∀ y' : CxPts q σ', u y' ∈ ptsIn p σ V → y' ∈ ptsIn q σ' W ∧ ev p σ V G (u y') = ev q σ' W g y')
    {B : LB Y} (ψ : Weight q σ' B) (hψ : ψ.IsCInf) :
    ReciprocityTheory.AnForm.M.IsPotential R.finAtlas (pot u hu hc ψ.locPot) := by
  refine ⟨fun x => (R.finAtlas_smoothOn_iff ((pot u hu hc ψ.locPot).isOpen_U x)).2 fun i v hv => ?_,
    fun x x' z hz => ?_⟩
  · by_cases hx : x ∈ Set.range u
    · obtain ⟨y, rfl⟩ := hx
      obtain ⟨hv, hv'⟩ := hv
      rw [Set.mem_preimage, pot_U_up] at hv'
      obtain ⟨y', hy', e⟩ := hv'
      refine (contDiffAt_chart_of_lifts hu hL (y := y') ?_ _ hv e.symm).contDiffWithinAt
      refine ((hψ _ y' hy').const_mul 2⁻¹).congr (Eventually.of_forall fun w => ?_)
      simp only [Function.comp_apply, pot_φ_up, Weight.locPot_φ]
      ring
    · have e : (pot u hu hc ψ.locPot).φ x = fun _ => 0 := funext (pot_φ_of_not hu hc _ hx)
      rw [e]
      exact contDiffWithinAt_const
  · by_cases hx : x ∈ Set.range u
    · obtain ⟨y, rfl⟩ := hx
      have hz₁ := hz.1
      rw [pot_U_up] at hz₁
      obtain ⟨w, hw, rfl⟩ := hz₁
      have hx' : x' ∈ Set.range u := by
        by_contra hx'
        have := hz.2
        rw [pot_U_of_not hu hc _ hx'] at this
        exact this (Set.mem_range_self w)
      obtain ⟨y', rfl⟩ := hx'
      have mem : ∀ (a b : CxPts q σ'), u b ∈ (pot u hu hc ψ.locPot).U (u a) → b ∈ ψ.locPot.U a := by
        intro a b hb
        rw [pot_U_up] at hb
        exact hu.injective.mem_set_image.1 hb
      have hw' := mem _ _ hz.2
      obtain ⟨V, G, hV, hG⟩ := hL _ (B.g (pick ψ.isLB y) (pick ψ.isLB y')).val w
        (mem_ptsIn_inf.2 ⟨hw, hw'⟩)
      obtain ⟨W, hW, hwW, hs, G', hG', e⟩ := (R.holoOn_ev V G).exists_log (isOpen_ptsIn _) hV
        (by rw [(hG w hV).2]; exact gv_ne_zero hw hw')
      refine ⟨W, hW, hwW, G', (R.finAtlas_holoOn_iff hW).2 hG', fun t ht => ?_⟩
      obtain ⟨s, rfl⟩ := pot_U_subset hu hc _ (Set.mem_range_self y) ht.1.2
      rw [e _ ht.1.1, (hG s (hs ht.1.1)).2, pot_φ_up, pot_φ_up, Weight.locPot_φ, Weight.locPot_φ,
        ψ.half_eq (mem _ _ ht.1.2) (mem _ _ ht.2), CxPts.gv, add_sub_cancel_left]
    · have hx' : x' ∉ Set.range u := fun hx' => by
        have := hz.1
        rw [pot_U_of_not hu hc _ hx] at this
        exact this (pot_U_subset hu hc _ hx' hz.2)
      refine ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const, fun t _ => ?_⟩
      rw [pot_φ_of_not hu hc _ hx, pot_φ_of_not hu hc _ hx']
      simp

end General

theorem isPotential_pot_up : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) [CompactSpace (CxPts (genStr Z) σ)] (hu : IsOpenEmbedding (up j hj σ)) (hc : IsClosed (Set.range (up j hj σ))), ClopenPush.LiftsFns j hj σ → ∀ {B : LB Y} (ψ : Weight q (σ.comp β) B), ψ.IsCInf → IsPotential (manifold Z σ).finAtlas (ClopenPush.pot (up j hj σ) hu hc ψ.locPot) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z _ Y q j hj σ _ hu hc hL B ψ hψ
  exact isPotential_pot_of_lifts _ hu hc hL ψ hψ

end GlobalTheory.ClopenPush

end
