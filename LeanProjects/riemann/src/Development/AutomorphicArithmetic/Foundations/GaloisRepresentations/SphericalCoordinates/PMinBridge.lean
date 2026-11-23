import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.minBridge_of :
    UpperTheory.Gal.W2.MinBridge := by
  intro p _ D G L β D' j hP ga c hga
  obtain ⟨hinj, hsmul, hspan, -⟩ := hP
  set f : 𝓞 D.F →+* G.F := (L.e : D.F →+* G.F).comp (algebraMap (𝓞 D.F) D.F) with hf
  have hpow : ∀ (n : ℕ) (u : D'.La), j ((ga ^ n) u) = (L.rep c ^ n) (j u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, hga, pow_succ, Module.End.mul_apply]
  have key : ∀ (q : (𝓞 D.F)[X]) (u : D'.La),
      j (q.sum fun i b => algebraMap (𝓞 D.F) D.O b • (ga ^ i) u) =
        L.rep (aeval c (q.map f)) (j u) := by
    intro q u
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.sum_def, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hpow, map_mul, map_pow, Module.End.mul_apply, ← L.rep_F]
    rfl
  have hK : ∀ q : (𝓞 D.F)[X], Kills (algebraMap (𝓞 D.F) D.O) ga q ↔ aeval c (q.map f) = 0 := by
    intro q
    constructor
    · intro h
      apply L.rep_inj
      rw [map_zero]
      refine LinearMap.ext fun w => ?_
      obtain ⟨m, u, hm, hmu⟩ := hspan w
      have h1 : L.rep (aeval c (q.map f)) (j u) = 0 := by rw [← key, h u, map_zero]
      have h2 : m • L.rep (aeval c (q.map f)) w = 0 := by
        rw [← LinearMap.map_smul_of_tower, hmu, h1]
      rw [← Nat.cast_smul_eq_nsmul ℚ] at h2
      rw [LinearMap.zero_apply]
      exact (smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm)
    · intro h x
      apply hinj
      rw [key, h, map_zero, LinearMap.zero_apply, map_zero]
  refine ⟨(minpoly.monic (Algebra.IsIntegral.isIntegral c)).map _, fun q => ?_⟩
  have hcomp : (L.e.symm : G.F →+* D.F).comp f = algebraMap (𝓞 D.F) D.F := by
    ext b
    simp [hf]
  rw [hK, ← minpoly.dvd_iff, ← map_dvd_iff (Polynomial.mapEquiv L.e.symm),
    Polynomial.mapEquiv_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, hcomp]
