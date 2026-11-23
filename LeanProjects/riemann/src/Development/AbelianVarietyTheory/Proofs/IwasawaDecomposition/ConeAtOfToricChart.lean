import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfMonomialMultipleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramifiedStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartCone

theorem isCN_chartRing (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] : IsCN (ChartRing k m e) := by
  have : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
  refine ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2, ?_, inferInstance⟩
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  exact GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

theorem symm_of_isCone {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {m : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (h : IsCone H.bar φ δ) : (∀ i y z, δ i y z = δ i z y) ∧ ∀ i, δ i ≠ 0 := by
  refine ⟨fun i => (h.mem i).1, fun i hi => h.basis.linearIndependent.ne_zero i ?_⟩
  exact Subtype.ext hi

theorem coneAt_of_hasChartOf : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ) (x : gen Y), GlobalTheory.MumfordChart.HasChartOf φ Y BD d x → GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (genι Y x) := by
  intro E _ _ _ H D l Xo c φ Y BD d x h
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, hx, h₁, -, -, ⟨μ⟩, h₅, -, h₆, h₇, -, -⟩ := h
  have : CharZero (ChartRing k m e) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  have : IsIso (genι Y) := inferInstance
  have hE := GlobalTheory.T.etaleCompletion_comp_iso ξ (genι Y) h₁
  obtain ⟨hs, hne⟩ := symm_of_isCone H φ h₆
  refine ⟨ChartRing k m e, inferInstance, inferInstance, inferInstance, ξ ≫ genι Y, t, μ, P, m, δ,
    isCN_chartRing k m e, ?_, hE, GlobalTheory.T.chart_ring_formally_unramified k m e _ hE,
    GlobalTheory.FlatTors.torsionIso_holds E H _ _ (GlobalTheory.MumfordChart.admissibleBase_chartRing k m e) t P, h₆,
    GlobalTheory.T.inCone_of_monomial_multiple P.D.toPre (bdParam k m e) (fun i => (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) δ l.M'
      (Nat.pos_of_ne_zero (GlobalTheory.MumfordChart.level_ne_zero l)) h₇ hs hne h₅⟩
  rw [← hx]; rfl

end GlobalTheory.ChartCone
