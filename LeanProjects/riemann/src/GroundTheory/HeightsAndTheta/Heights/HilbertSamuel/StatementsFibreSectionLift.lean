import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreSectionLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 1) →
    ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z

theorem FibreSectionLift.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := PtIdx) unitPoint) (0 + 1) ∧ Nat.Prime 2 ∧
      Subsingleton (KH.cechHc PtIdx (KH.quotPart (ZMod 2) (fibreIdeal (ι := PtIdx) 2 unitPoint))
        (fun _ => (1 : ℤ)) 1) := by
  refine ⟨unitPoint_isArithVar, Nat.prime_two, ?_⟩
  have := cechC_one_subsingleton (ZMod 2)
    (MRingOver (ZMod 2) PtIdx ⧸ fibreIdeal (ι := PtIdx) 2 unitPoint)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

end GroundTheory.Heights₂.Heights.HilbertSamuel
