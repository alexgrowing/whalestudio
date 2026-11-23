import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundaryStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_point_vanishing_of_isMaximal {X : Scheme} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (hm : m.IsMaximal) : ∃ x, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ X.basicOpen f := by
  let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
  refine ⟨U.2.fromSpec p, ?_, ?_⟩
  · have h : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
    rw [U.2.range_fromSpec] at h
    exact h
  · intro f hf hx
    have h : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hx
    rw [U.2.fromSpec_preimage_basicOpen] at h
    exact h hf

theorem logKS_inj_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm hKS hΘ
  have hp := exists_point_vanishing_of_isMaximal U m hm
  obtain ⟨x, hxU, hxm⟩ := hp
  by_cases hx : x ∈ LogKS.interior Y
  · exact GlobalTheory.T.kodairaSpencer_injective_closed_interior_point E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
      ⟨x, hx, hxU, hxm⟩ hKS hΘ
  · have hb : ∃ x, x ∉ LogKS.interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f := ⟨x, hx, hxU, hxm⟩
    have key := GlobalTheory.T.logKodairaSpencer_injective_mod_maximal_boundary E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
    first
      | exact key hb hKS hΘ
      | exact key hKS hΘ

end GlobalTheory
