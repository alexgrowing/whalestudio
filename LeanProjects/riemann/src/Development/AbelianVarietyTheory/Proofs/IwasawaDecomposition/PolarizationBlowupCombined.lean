import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupPolarizationAmpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupPolarizationDegreeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MixedOrder

theorem idlAlong_comap {X X' : Scheme.{0}} (J : X.IdealSheafData) (π : X' ⟶ X) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ X') : idlAlong (J.comap π) χ = idlAlong J (χ ≫ π) := by
  unfold idlAlong
  rw [GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

theorem ordAlong_mixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be ∧ idlAlong EX.idealSheaf χ = Ideal.span {ϖ ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 hB W _ _ _ hW hp ϖ hϖ χ t ht P hj
    be hbe hmon
  obtain ⟨m, hm, hle⟩ := GlobalTheory.T.blowup_polarization_ample E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 hB W hW hp
    ϖ hϖ χ t ht P hj be hbe hmon
  refine ⟨m, hm, ?_⟩
  rw [hB.2.2.2.2.1, idlAlong_comap]
  exact le_antisymm (GlobalTheory.T.blowup_polarization_degree E H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX h1 h2 h3 h4 h5 h6 h7 h8 hB W hW hp
    ϖ hϖ χ t ht P hj be hbe hmon m hm) hle

end GlobalTheory.MixedOrder
