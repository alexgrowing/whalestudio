import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.MumfordChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasChart (Z : Model Xo c β) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m d)))
    (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (γ : Fin m → levelForms H l.M' P.D.toPre.X),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m d i} ∧
    (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m d) (fun i => γ i) ∧ IsPartOfBasis γ

theorem admissibleBase_chartRing (k : Type) [Field k] (m d : ℕ) :
    AdmBase (ChartRing k m d) (maximalIdeal (ChartRing k m d)) := by
  let e : MvPowerSeries (Fin (m + d)) k ≃+* ChartRing k m d :=
    (MvPowerSeries.renameEquiv k finSumFinEquiv.symm).toRingEquiv
  have h₁ := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries k (m + d)
  have : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]; infer_instance
  have h₂ := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries k (m + d)
  exact ⟨isNoetherianRing_of_ringEquiv _ e, inferInstance, IsIntegrallyClosed.of_equiv e,
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv e⟩

theorem hasChart_iff (Z : Model Xo c β) (x : gen Z) : HasChart Z x ↔ HasToricChart Z x := by
  constructor
  · rintro ⟨k, _, m, d, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄, h₅, h₆⟩
    have : CharZero (ChartRing k m d) :=
      (Spec.preimage (ξ ≫ genStr Z)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
    exact ⟨k, _, m, d, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄,
      GlobalTheory.FlatTors.torsionIso_holds E H _ _ (admissibleBase_chartRing k m d) t P, h₅, h₆⟩
  · rintro ⟨k, _, m, d, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄, -, h₅, h₆⟩
    exact ⟨k, _, m, d, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MumfordChart

namespace GlobalTheory.Published

def ToroidalCharts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          ∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChart Y x

theorem ToroidalCharts.exists_model (h : ToroidalCharts) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (RingHom.id c.F),
      SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧ ∀ x ∈ genBd Y, HasToricChart Y x := by
  obtain ⟨Y, h₁, h₂, h₃⟩ := h E H Dw hr l Xo c
  exact ⟨Y, h₁, h₂, fun x hx => (GlobalTheory.MumfordChart.hasChart_iff Y x).1 (h₃ x hx)⟩

end GlobalTheory.Published
