import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.memDual_of :
    UpperTheory.Gal.W2.TrDual → UpperTheory.Gal.W2.MemDual := by
  intro h p _ G
  choose d hd0 hd using fun w : Fin G.m => h p G w
  refine ⟨d, hd0, fun a => ?_⟩
  constructor
  · intro ha w i
    have key := (hd w (a w i)).1 (fun z0 hz0 => by
      have hz : IntL (Pi.single w (Pi.single i z0) : Loc G) := by
        intro w' j
        by_cases hw : w' = w
        · subst hw
          by_cases hj : j = i
          · subst hj
            simpa using hz0
          · simp [Pi.single_apply, hj]
        · simp [Pi.single_apply, hw]
      have hp := ha _ hz
      have he : pairL a (Pi.single w (Pi.single i z0) : Loc G) =
          Algebra.trace ℚ_[p] (G.Fw w) (a w i * z0) := by
        unfold pairL
        rw [Finset.sum_eq_single w]
        · simp
        · intro w' _ hw'
          simp [Pi.single_apply, hw']
        · simp
      rwa [he] at hp)
    simpa [mul_comm] using key
  · intro ha z hz
    unfold pairL
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro w _
    simp only [dotProduct, map_sum]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    have hai : ‖((a w i * d w : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
      simpa [mul_comm] using ha w i
    exact (hd w (a w i)).2 hai (z w i) (hz w i)
