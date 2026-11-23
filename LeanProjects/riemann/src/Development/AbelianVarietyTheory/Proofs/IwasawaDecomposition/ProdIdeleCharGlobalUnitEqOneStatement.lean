import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_idele_char_global_unit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Ideles F →* B), IsOpen (ψ.ker : Set (Ideles F)) → (∀ k : Fˣ, ψ (diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  first | exact @GlobalTheory.ProdLocUnit.prod_locUnit_eq_one | exact GlobalTheory.ProdLocUnit.prod_locUnit_eq_one | (intros; apply GlobalTheory.ProdLocUnit.prod_locUnit_eq_one <;> assumption)
