import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

theorem resBridge : ResBridgeStatement := by
  intro K _ ι _ P J e R Ψ L A s hP hΨ hL hA hs
  haveI := R.compact
  haveI := R.t2

  have key := pushForward_null R.A (fun j => potOf R (L j))
    (fun j => potOf_isPotential R (L j) (hL j)) (brQ R Ψ) (brBad R Ψ)
    (brBad_null R Ψ hP hΨ)
    (fun x hx j hj => by
      by_contra h
      apply hx
      simp only [brBad, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inr ⟨j, hj, h⟩)
    (brFib_finite (R := R) (Ψ := Ψ) hP hΨ) _ (brIntegrable R L A s hP hL hA hs)
  rw [key]
  unfold ptsIntegralAt

  exact MeasureTheory.integral_congr_ae (brFibreSum_ae R Ψ L A s hP hΨ hL hA hs)

end ReciprocityTheory.ChartRestriction.G.Geo
