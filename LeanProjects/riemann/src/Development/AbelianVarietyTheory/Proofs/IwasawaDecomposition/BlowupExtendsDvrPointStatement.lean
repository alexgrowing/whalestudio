import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupExtendsDvrPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blowup_extends_dvr_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n : ℕ), IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ gen Y) (t : SAB H (Sp W)), SABMap t Y.t (χ ≫ genι Y) → Set.range (jK W ≫ χ ≫ genι Y) ⊆ Set.range Y.j → Nonempty (SABMap t X.t (χ ≫ e.hom ≫ genι Z ≫ π)) ∧ Set.range (jK W ≫ χ ≫ e.hom ≫ genι Z ≫ π) ⊆ Set.range X.j := by
  first | exact @GlobalTheory.TorRef.blow_sabMap_trait | exact GlobalTheory.TorRef.blow_sabMap_trait | (intros; apply GlobalTheory.TorRef.blow_sabMap_trait <;> assumption)
