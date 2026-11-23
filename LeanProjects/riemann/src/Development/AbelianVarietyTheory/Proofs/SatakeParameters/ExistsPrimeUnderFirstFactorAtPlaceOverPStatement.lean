import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverP
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E), PrimeOf p (G.P.W v) (A.iw v) P ∧ (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧ ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | exact GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | (intros; apply GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place <;> assumption)
