import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (w : HeightOneSpectrum (𝓞 F)) (x x' : GL (Fin N) (AfE F E)), SameOff w x x' → ∃ m : ℕ, ∀ c : 𝓞 F, c ∈ w.asIdeal ^ m → ∀ y ∈ latAd x Lb, (algebraMap F E (c : F)) • y ∈ latAd x' Lb := by
  first | exact @GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | exact GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff <;> assumption)
