import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_mul_spherical_coordinates {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

private theorem det_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    (A.map star).det = star A.det := by
  exact (RingHom.map_det (starRingEnd ℂ) A).symm

private theorem hermForm_mulVec_mulVec {g : ℕ} (M H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (H *ᵥ z) (H *ᵥ w) = hermForm (Hᵀ * M * H.map star) z w := by
  rw [PerCoordU.herm_mulVec_left, PerCoordU.herm_mulVec_right]

private theorem eq_of_mulVec_period_eq {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, A *ᵥ P x = B *ᵥ P x) : A = B := by
  have e := PerCoordU.ext_per hP (f := PeriodCoord.realMap A 0) (f' := PeriodCoord.realMap B 0)
    (fun x => by simp [PeriodCoord.realMap_apply, h])
  exact (PeriodCoord.realMap_inj e).1

private theorem eq_of_hermForm_im_eq_on_periods {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {N N' : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x y, (hermForm N (P x) (P y)).im = (hermForm N' (P x) (P y)).im) : N = N' := by
  apply PerCoordU.sesq_ext
  have h1 : PeriodCoord.imForm N = PeriodCoord.imForm N' := by
    apply PerCoordU.ext_per hP
    intro x
    apply PerCoordU.ext_per hP
    intro y
    simp only [PeriodCoord.imForm_apply]
    exact h x y
  intro z w
  rw [← PeriodCoord.imForm_apply, ← PeriodCoord.imForm_apply, h1]

private theorem inv_mul_comm_of_mul_comm_of_det_unit {g : ℕ} (X N : Matrix (Fin g) (Fin g) ℂ) (hN : IsUnit N.det)
    (h : X * N = N * X) : N⁻¹ * X = X * N⁻¹ := by
  calc N⁻¹ * X = N⁻¹ * X * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
    _ = N⁻¹ * (X * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = N⁻¹ * (N * X) * N⁻¹ := by rw [h]
    _ = X * N⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN, Matrix.one_mul]

theorem UpperTheory.Gal.W2.adExists_of :
    UpperTheory.Gal.W2.AdExists := by
  intro O _ bar g ρ D P₀ M₀ hP hM ga H hF
  obtain ⟨⟨m, hm, hEF⟩, hga⟩ := hF
  obtain ⟨_, hpos, hIm⟩ := hM
  have hform : Hᵀ * M₀ * H.map star = (m : ℂ) • M₀ := by
    apply eq_of_hermForm_im_eq_on_periods hP
    intro x y
    have hs : hermForm ((m : ℂ) • M₀) (P₀ x) (P₀ y) = (m : ℂ) * hermForm M₀ (P₀ x) (P₀ y) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
    rw [← hermForm_mulVec_mulVec, ← hga x, ← hga y, hIm, hEF, hs, Complex.mul_im, hIm]
    simp
  have hdM : M₀.det ≠ 0 := PeriodCoord.det_ne_zero_of_pos hpos
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hform
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, det_map_star',
      Matrix.det_smul] at e
    simp [hdM, hm.ne'] at e
  have hcomm : ∀ a, ρ a * H = H * ρ a := by
    intro a
    apply eq_of_mulVec_period_eq hP
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hga x, ← hP.1 a (ga x), ← hP.1 a x,
      ← hga (a • x), LinearMap.map_smul]
  refine ⟨hdet, hcomm, ?_⟩
  intro C hC
  set N := H.map star with hNdef
  have hNu : IsUnit N.det := by
    rw [hNdef, det_map_star']
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  have hNtu : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
  have hc' : ∀ b, (ρ b).map star * N = N * (ρ b).map star := by
    intro b
    rw [hNdef, ← map_star_mul_spherical_coordinates, ← map_star_mul_spherical_coordinates, hcomm]
  have hC' : (Cᵀ * M₀)ᵀ = Cᵀ * M₀ ∧
      ∀ a, Cᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * (Cᵀ * M₀) := hC
  obtain ⟨hS1, hS2⟩ := hC'
  have hHM : Hᵀ * M₀ = (m : ℂ) • (M₀ * N⁻¹) := by
    calc Hᵀ * M₀ = Hᵀ * M₀ * N * N⁻¹ := by
          rw [Matrix.mul_assoc (Hᵀ * M₀), Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
      _ = (m : ℂ) • (M₀ * N⁻¹) := by rw [hform, Matrix.smul_mul]
  have hkey : (H * C * N⁻¹)ᵀ * M₀ = (m : ℂ) • (N⁻¹ᵀ * (Cᵀ * M₀) * N⁻¹) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hHM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  show ((H * C * N⁻¹)ᵀ * M₀)ᵀ = (H * C * N⁻¹)ᵀ * M₀ ∧
    ∀ a, (H * C * N⁻¹)ᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * ((H * C * N⁻¹)ᵀ * M₀)
  rw [hkey]
  generalize Cᵀ * M₀ = S at hS1 hS2 ⊢
  constructor
  · simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hS1,
      Matrix.mul_assoc]
  · intro a
    have c1 : N⁻¹ * (ρ (bar a)).map star = (ρ (bar a)).map star * N⁻¹ :=
      inv_mul_comm_of_mul_comm_of_det_unit _ N hNu (hc' (bar a))
    have hX : (ρ a)ᴴ * Nᵀ = Nᵀ * (ρ a)ᴴ := by
      rw [← PerCoordU.map_star_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hc' a]
    have c2 : Nᵀ⁻¹ * (ρ a)ᴴ = (ρ a)ᴴ * Nᵀ⁻¹ := inv_mul_comm_of_mul_comm_of_det_unit _ _ hNtu hX
    rw [Matrix.transpose_nonsing_inv]
    calc (m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹) * (ρ (bar a)).map star
        = (m : ℂ) • (Nᵀ⁻¹ * S * (N⁻¹ * (ρ (bar a)).map star)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (S * (ρ (bar a)).map star) * N⁻¹) := by
          rw [c1]; simp only [Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * ((ρ a)ᴴ * S) * N⁻¹) := by rw [hS2 a]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (ρ a)ᴴ * S * N⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (ρ a)ᴴ * ((m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹)) := by
          rw [c2]; simp only [Matrix.mul_smul, Matrix.mul_assoc]
