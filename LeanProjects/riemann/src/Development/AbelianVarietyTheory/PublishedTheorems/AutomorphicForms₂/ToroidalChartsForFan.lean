import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.MumfordChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasChartOf (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (BD : EffCartierData Z.X) (d : ℕ) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (ξ : Sp (ChartRing k m e) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (γ : Fin m → levelForms H l.M' P.D.toPre.X)
    (δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin m → ℕ),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m e i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m e i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m e) (fun i => γ i) ∧
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q ∧
    IsCone H.bar φ δ ∧ (∀ i, (γ i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
    idlAlong BD.idealSheaf (ξ ≫ genι Z) = Ideal.span {∏ i, bdParam k m e i ^ a i}

variable {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {BD : EffCartierData Z.X} {d : ℕ} {x : gen Z}

theorem level_ne_zero (l : Geo.Tor.Level H) : l.M' ≠ 0 :=
  (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos).ne'

theorem HasChartOf.hasChart (h : HasChartOf φ Z BD d x) : HasChart Z x := by
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, hx, h₁, h₂, h₃, h₄, h₅, -, h₆, h₇, -⟩ := h
  exact ⟨k, _, m, e, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄, h₅, h₆.isPartOfBasis_level (level_ne_zero l) h₇⟩

theorem HasChartOf.exists_isToricChart (h : HasChartOf φ Z BD d x) :
    ∃ (k : Type) (_ : Field k) (m e : ℕ) (ξ : Sp (ChartRing k m e) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m e)))
      (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (γ : Fin m → levelForms H l.M' P.D.toPre.X)
      (δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin m → ℕ),
      ξ (closedPoint _) = x ∧ IsToricChart Z ξ P γ ∧ Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q ∧
      IsCone H.bar φ δ ∧ (∀ i, (γ i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i) ∧
      (∀ i, (a i : ℝ) = d * φ.evalZ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
      idlAlong BD.idealSheaf (ξ ≫ genι Z) = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, hx, h₁, h₂, h₃, h₄, h₅, h₀, h₆, h₇, h₈⟩ := h
  have : CharZero (ChartRing k m e) :=
    (Spec.preimage (ξ ≫ genStr Z)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  exact ⟨k, _, m, e, ξ, t, P, γ, δ, a, hx, ⟨h₁, h₂, h₃, h₄,
    GlobalTheory.FlatTors.torsionIso_holds E H _ _ (admissibleBase_chartRing k m e) t P, h₅,
    h₆.isPartOfBasis_level (level_ne_zero l) h₇⟩, h₀, h₆, h₇, h₈⟩

end GlobalTheory.MumfordChart

namespace GlobalTheory.Published

def ToroidalChartsForFan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD))

namespace ToroidalChartsForFan

theorem toroidalCharts (h : ToroidalChartsForFan)
    (hφ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ),
      ∃ φ : InvFun (𝓞 E), IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ) : ToroidalCharts := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φ, h₁, h₂⟩ := hφ E H (min Dw.p Dw.q)
  obtain ⟨Y, BD, d, k, -, -, h₃, h₄, -, h₅, -⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, h₃, h₄, fun x hx => (h₅ x hx).hasChart⟩

theorem exists_model (h : ToroidalChartsForFan) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {φ : InvFun (𝓞 E)} (h₁ : IsPolFan H.bar (min Dw.p Dw.q) φ)
    (h₂ : NoSelfInt H.bar (min Dw.p Dw.q) φ) {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
      SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
      (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
      (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
      (PushInvertible Y.t.G Y.t.PP.L → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD)) := by
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, fun hP => a₇ (GlobalTheory.FlagMod.isLB_detOm hP)⟩

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (h : Dw.q = 0)
    (φ : InvFun (𝓞 E)) : IsPolFan H.bar (min Dw.p Dw.q) φ ∧ NoSelfInt H.bar (min Dw.p Dw.q) φ := by
  rw [h, Nat.min_zero]
  exact ⟨isPolFan_zero, noSelfInt_zero⟩

end ToroidalChartsForFan

end GlobalTheory.Published
