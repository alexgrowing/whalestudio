import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.EtaForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in

theorem _root_.GlobalTheory.EtaForm.etaValAt_evR_of_fromTest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → _root_.GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : _root_.Formalism.L2.Pj.Rul Xo c), _root_.GlobalTheory.EtaForm.IsEtaRule Xo c R cf xs f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : _root_.Formalism.L2.Pj.FrPt Xo c S), _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y (_root_.Formalism.L2.Pj.evR Xo c f y) ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (z : _root_.Formalism.L2.Pj.FrPt Xo c S'), _root_.Formalism.L2.Pj.FrMap φ y z → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs z (φ (_root_.Formalism.L2.Pj.evR Xo c f y)) := by
  intro E _ _ _ H Dw l Xo c R hR J _ n cf xs f hf S _ _ y hy
  have hlaws := _root_.GlobalTheory.EtaForm.etaValAt_existsUnique_natural _root_.GlobalTheory.firstFiveLaws.1
    E H Dw l Xo c R hR J n cf xs
  have transport : ∀ (S₀ S₁ : Type) [CommRing S₀] [Algebra c.F S₀] [CommRing S₁] [Algebra c.F S₁]
      (φ : S₀ →ₐ[c.F] S₁) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c S₀) (y₁ : _root_.Formalism.L2.Pj.FrPt Xo c S₁) (v : S₀),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y₁ → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ v →
        _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₁ (φ v) := by
    intro S₀ S₁ _ _ _ _ φ y₀ y₁ v hφ hv
    obtain ⟨w, hw, -⟩ := hlaws.1 S₁ y₁
    rwa [hlaws.2 S₀ S₁ φ y₀ y₁ hφ v w hv hw]
  have key : ∃ (p : _root_.Formalism.L2.Pj.TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y ∧ _root_.Formalism.L2.Pj.evR Xo c f y = φ (f p y₀) := by
    refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
      hy.choose_spec.choose_spec.choose_spec, ?_⟩
    unfold _root_.Formalism.L2.Pj.evR _root_.Formalism.L2.Pj.evalAt
    rw [dif_pos hy]
  obtain ⟨p, φ, y₀, hφ, hval⟩ := key
  have h₀ : _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ (f p y₀) := hf p y₀
  refine ⟨hval ▸ transport _ _ φ y₀ y _ hφ h₀, ?_⟩
  intro S' _ _ ψ z hz
  rw [hval]
  exact transport _ _ (ψ.comp φ) y₀ z _ (_root_.GlobalTheory.FramedBaseChange.trans φ ψ hφ hz) h₀

end GlobalTheory.EtaForm
