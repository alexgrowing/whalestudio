import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_base_change_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X) (hπ : π ≫ Z.s = Z'.s ≫ spMap b)
    (mu : TwMap σ Z'.t Z.t π), GlobalTheory.IsAmpleLB (polOf Z m BD) → GlobalTheory.IsAmpleLB (polOf Z' m BD') →
    BD'.idealSheaf = BD.idealSheaf.comap π → IsFinite (pullback.lift π Z'.s hπ) := by
  first | exact @GlobalTheory.PolFin.isFinite_lift | exact GlobalTheory.PolFin.isFinite_lift | (intros; apply GlobalTheory.PolFin.isFinite_lift <;> assumption)
