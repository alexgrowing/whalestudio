import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrPointLifting
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_point_lifting : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g] (a : O →+* K), Function.Injective a → g ≫ s = spMap a → ∀ d : ℕ, (letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) → ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧ spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  first | exact @GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe | exact GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe | (intros; apply GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe <;> assumption)
