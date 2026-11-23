import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
