import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.killsMat_of :
    UpperTheory.Gal.W2.KillsMat := by
  intro F _ _ O _ bar g ρ a D P₀ hP ga H hH q
  have hpow : ∀ (i : ℕ) (x : D.La), P₀ ((ga ^ i) x) = (H ^ i) *ᵥ P₀ x := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hH, Matrix.mulVec_mulVec, pow_succ]
  have hsum : ∀ x, P₀ (q.sum fun i b => a b • (ga ^ i) x) =
      (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x := by
    intro x
    simp only [Polynomial.sum_def, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP.1, hpow, Matrix.mulVec_mulVec]
  constructor
  · intro hk
    have hz : ∀ x, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x = 0 := fun x => by
      rw [← hsum, hk x, map_zero]
    have hlin : (Matrix.mulVecLin (q.sum fun i b => ρ (a b) * H ^ i)).restrictScalars ℝ = 0 :=
      GlobalTheory.PerCoordU.ext_per hP fun x => by simpa using hz x
    have hv : ∀ v, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ v = 0 := fun v => by
      simpa using LinearMap.congr_fun hlin v
    exact Matrix.mulVec_injective (funext fun v => by rw [hv v, Matrix.zero_mulVec])
  · intro h x
    apply hP.2.1
    rw [hsum, h, map_zero, Matrix.zero_mulVec]
