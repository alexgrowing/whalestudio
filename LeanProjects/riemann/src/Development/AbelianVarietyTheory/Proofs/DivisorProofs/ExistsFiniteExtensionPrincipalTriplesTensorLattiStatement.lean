import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLatti
import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_principalTriples_tensorLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (A B : PAT H (Sp (𝓞 K))) (r s : ℕ),
    ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ r 0 → HasType H B.t.act ρ s 0 →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (ω : 𝓞 K') (C : Ell H (𝓞 K') ω)
      (A' B' : PAT H (Sp (𝓞 K'))) (_ : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
      (_ : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (DA DB : Datum H)
      (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H),
      DA.p + DA.q = r ∧ DB.p + DB.q = s ∧ Nonempty (IsTen C DA hA A') ∧ Nonempty (IsTen C DB hB B') := by
  first | exact @GlobalTheory.CM.TenPair.exists_isTen_pair | exact GlobalTheory.CM.TenPair.exists_isTen_pair | (intros; apply GlobalTheory.CM.TenPair.exists_isTen_pair <;> assumption)
