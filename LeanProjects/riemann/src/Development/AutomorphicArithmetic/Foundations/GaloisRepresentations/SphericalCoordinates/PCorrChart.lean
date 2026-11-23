import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_inv_mul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hdet : H.det ≠ 0) :
    (H.map star)⁻¹ * H.map star = 1 := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hb : H.map star * (H⁻¹).map star = 1 := by
    have h := congrArg (fun M => (starRingEnd ℂ).mapMatrix M) hHi
    simp only [map_mul, map_one] at h
    exact h
  have hi : (H.map star)⁻¹ = (H⁻¹).map star := Matrix.inv_eq_right_inv hb
  rw [hi]
  exact mul_eq_one_comm.mp hb

theorem UpperTheory.Gal.W2.corrChart_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart := by
  intro hAd hLin hFib O _ bar g ρ D X s A _ S k Z c₁ c₂ P₀ M₀ hP₀ hM₀ ga H hH L hL C hC hC'' z
  obtain ⟨hdet, hcomm, -⟩ := hAd O bar g ρ D P₀ M₀ hP₀ hM₀ ga H hH
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hiH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hu
  have hbi := map_star_inv_mul H hdet
  set C'' := H * C * (H.map star)⁻¹ with hC''def

  let P'' : D.La →+ (Fin g → ℂ) := (Matrix.toLin' H⁻¹).toAddMonoidHom.comp (perC P₀ C'')
  have hP''apply : ∀ x, P'' x = H⁻¹ *ᵥ perC P₀ C'' x := fun x => by
    show Matrix.toLin' H⁻¹ (perC P₀ C'' x) = _
    rw [Matrix.toLin'_apply]
  have hdetInv : (H⁻¹).det ≠ 0 := by
    intro h0
    have h1 : (H⁻¹ * H).det = 1 := by rw [hiH, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hcommInv : ∀ a, ρ a * H⁻¹ = H⁻¹ * ρ a := fun a => by
    calc ρ a * H⁻¹ = H⁻¹ * (H * ρ a) * H⁻¹ := by
            rw [← Matrix.mul_assoc, hiH, Matrix.one_mul]
      _ = H⁻¹ * (ρ a * H) * H⁻¹ := by rw [hcomm a]
      _ = H⁻¹ * ρ a * (H * H⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * ρ a := by rw [hHi, Matrix.mul_one]
  have hP'' : IsPeriod D ρ P'' :=
    hLin O bar g ρ D (perC P₀ C'') P'' H⁻¹ hC'' hdetInv hcommInv hP''apply
  have hga : ∀ x, P'' (ga x) = perC P₀ C x := fun x => by
    rw [hP''apply, perC_apply, perC_apply, hH.2 x, GlobalTheory.PerCoordU.star_mulVec_map,
      Matrix.mulVec_mulVec, hC''def]
    have e : H * C * (H.map star)⁻¹ * H.map star = H * C := by
      rw [Matrix.mul_assoc, hbi, Matrix.mul_one]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hcorr := hL (perC P₀ C) P'' hC hP'' hga z
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' H) (Matrix.toLin' H⁻¹)
    (by rw [← Matrix.toLin'_mul, hHi, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hiH, Matrix.toLin'_one])
  have happ : ∀ v, h v = H *ᵥ v := fun v => by
    show Matrix.toLin' H v = _
    rw [Matrix.toLin'_apply]
  have hfib := (hFib O bar g ρ D X s A S k P'' hP'').2.2.2.2 (perC P₀ C'') h hC''
    (fun x => by rw [happ, hP''apply, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]) (L z)
  have hz : fibMap H L z = fun j => h (L z j) := by
    funext j
    rw [happ]
    simp [fibMap, Matrix.toLin'_apply]
  rw [hz, hfib]
  exact hcorr
