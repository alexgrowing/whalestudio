import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRationalInjectivityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAffineOpenUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFibresCharUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTensorVanishingLocalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem rTensor_eq_zero_of_restrict_affine_inf : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens), Flat s →
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
    pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
  ∀ (W : M.Opens), IsAffineOpen W → ∀ (L : Type) [AddCommGroup L] (h : Γ(M, W) ⊗[ℤ] L),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor L (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  intro N M s V hs hn hc W hW L _ h hh
  have hA := GlobalTheory.T.flat_affine_open_units N M s hs W hW
  exact GlobalTheory.T.tensor_rational_injectivity N {W' : M.Opens // IsAffineOpen W' ∧ W' ≤ W ⊓ V} Γ(M, W) (fun i => Γ(M, i.1))
    (fun i => (M.presheaf.map (homOfLE (i.2.2.trans inf_le_left)).op).hom) hA.1
    (fun i => (GlobalTheory.T.flat_affine_open_units N M s hs i.1 i.2.1).1) hA.2
    (fun hN0 h' hh' => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.normal_fibres_char_unit N M s V hn hc ℚ (by exact_mod_cast hN0) W hW
      exact GlobalTheory.T.rational_tensor_vanishing_local M V W hW ℚ h1 h2 h' (fun W' hW' hle => hh' ⟨W', hW', hle⟩))
    (fun p hp hpN h' hh' => by
      haveI := Fact.mk hp
      obtain ⟨h1, h2⟩ := GlobalTheory.T.normal_fibres_char_unit N M s V hn hc (ZMod p) (by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpN) W hW
      exact GlobalTheory.T.rational_tensor_vanishing_local M V W hW (ZMod p) h1 h2 h' (fun W' hW' hle => hh' ⟨W', hW', hle⟩))
    L h (fun i => hh i.1 i.2.1 i.2.2)

end GlobalTheory.RealMult
