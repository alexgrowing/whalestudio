import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.stabTriv_of :
    UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.Rigid → UpperTheory.Gal.W2.StabTriv := by
  intro hOcc hLat hFix hRig p _ D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N hN3 hNp B a y hSees
  obtain ⟨D', t, P, j, hCls, hPer, hPl, hCA, hLoc, Q, hQ, hQj, hrel⟩ :=
    hOcc p D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N (by omega) hNp B a
  obtain ⟨hFixL, hS1, hS2⟩ := hSees
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B (PD B) N (by omega) hNp D' t D' t j j a.1 a.1 N N t t
      hCls hCls hPl hPl hCA hCA hLoc hLoc y).mp ⟨hS1, hS2⟩
  obtain ⟨hiff, hinv⟩ := hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y
  obtain ⟨H, hH⟩ := hiff.mp hFixL
  obtain ⟨H', hH'⟩ := ((hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y⁻¹).1).mp (hinv hFixL)
  have hback : ∀ x : VQ D, (actY L y⁻¹) ((actY L y) x) = x := by
    intro x
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have key : ∀ z, (H' * H) *ᵥ z = z := by
    let f : (Fin D.g → ℂ) →ₗ[ℝ] (Fin D.g → ℂ) :=
      (Matrix.toLin' (H' * H)).restrictScalars ℝ - LinearMap.id
    have hle : Set.range Q ⊆ LinearMap.ker f := by
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show Matrix.toLin' (H' * H) (Q x) - Q x = 0
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hH x, ← hH', hback, sub_self]
    intro z
    have hz : z ∈ LinearMap.ker f := by
      have hs := Submodule.span_le.mpr hle
      rw [hQ.2.1] at hs
      exact hs Submodule.mem_top
    rw [LinearMap.mem_ker] at hz
    have hz' : Matrix.toLin' (H' * H) z - z = 0 := hz
    rwa [Matrix.toLin'_apply, sub_eq_zero] at hz'
  have hHH : H' * H = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact LinearMap.ext fun z => by rw [Matrix.toLin'_apply, key]; rfl
  letI : Invertible H := invertibleOfLeftInverse H H' hHH
  have hfix : ∀ u, w u = u :=
    hRig D.O D.inv D.g ρ D.La N D' t P w (Matrix.toLinearEquiv' H this) hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D' t hCls) hPer hwm
      (fun u => by
        rw [← hQj (w u), hwj, hH, hQj]
        show H *ᵥ P u = Matrix.toLin' H (P u)
        rw [Matrix.toLin'_apply])
  have hrep : L.rep ↑(↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, u, hm, hmu⟩ := hPl.2.2.1 x
    have h1 : m • (actY L y) x = m • x := by
      rw [← map_nsmul, hmu, ← hwj, hfix]
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hm) h1
  have hy1 : (↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply Units.ext
    apply L.rep_inj
    rw [hrep, Units.val_one, map_one]
  have hprop := y.2
  obtain ⟨hy, -⟩ := hprop
  rw [hy1] at hy
  have hsh : sh G (1 : G.C) = 1 := by simp [sh]
  rw [Units.val_one, _root_.one_mul, hsh, _root_.mul_one] at hy
  have hq : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    have : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) * ↑B.β = 1 * ↑B.β := by rw [_root_.one_mul, ← hy]
    exact (Units.mul_left_inj B.β).mp this
  have hq' : ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    rw [← map_one (algebraMap ℚ G.C)] at hq
    exact (algebraMap ℚ G.C).injective hq
  apply Subtype.ext
  exact Prod.ext hy1 (Units.ext hq')
