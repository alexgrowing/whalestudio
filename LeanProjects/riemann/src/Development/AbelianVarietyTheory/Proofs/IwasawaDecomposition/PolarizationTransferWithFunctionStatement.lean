import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_transfer_with_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' → ∀ π : Z'.X ⟶ Z.X, Z'.j ≫ π = r ≫ Z.j →
    BD'.idealSheaf = BD.idealSheaf.comap π := by
  first | exact @GlobalTheory.PolDiv.idealSheaf_eq_comap | exact GlobalTheory.PolDiv.idealSheaf_eq_comap | (intros; apply GlobalTheory.PolDiv.idealSheaf_eq_comap <;> assumption)
