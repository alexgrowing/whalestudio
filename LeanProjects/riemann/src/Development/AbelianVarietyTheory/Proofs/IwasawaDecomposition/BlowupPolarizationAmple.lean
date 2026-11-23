import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorAmpleCriterionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorPolarizationPosStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorLineBundleTrivialStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MixedLower

theorem lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be ∧ Ideal.span {ϖ ^ m} ≤ idlAlong J (χ ≫ π) := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 h9 W _ _ _ hW hp ϖ hϖ χ t ht P hχ be hbe hmon
  obtain ⟨m, hm⟩ := GlobalTheory.T.blowup_divisor_ample_criterion E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 h9 W hW hp ϖ hϖ χ t
    ht P hχ be hbe hmon
  exact ⟨m, hm, GlobalTheory.T.blowup_divisor_line_bundle_trivial E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 h9
    (GlobalTheory.T.blowup_divisor_polarization_pos E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 h9) W hW hp ϖ hϖ χ t ht P hχ be
    hbe hmon m hm⟩

end GlobalTheory.MixedLower
