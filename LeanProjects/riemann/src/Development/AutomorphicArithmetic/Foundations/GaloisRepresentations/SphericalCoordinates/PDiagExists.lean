import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem sep_of_integer {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem UpperTheory.Gal.W2.diagExists_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.HSep → UpperTheory.Gal.W2.DiagExists := by
  intro hSim hExt hKills hHSep F _ _ O _ bar g ρ a D P₀ hP ga H hH χ hmin hsep
  have hcomm : ∀ c : 𝓞 F, ρ (a c) * H = H * ρ (a c) := by
    intro c
    have hx : ∀ x : D.La, (ρ (a c) * H) *ᵥ P₀ x = (H * ρ (a c)) *ᵥ P₀ x := by
      intro x
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hH x, ← hP.1 (a c) (ga x),
        ← hP.1 (a c) x, ← hH (a c • x), LinearMap.map_smul]
    have hlin := GlobalTheory.PerCoordU.ext_per hP
      (f := ((ρ (a c) * H).mulVecLin).restrictScalars ℝ)
      (f' := ((H * ρ (a c)).mulVecLin).restrictScalars ℝ) (fun x => by simpa using hx x)
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hlin z
    simpa using hz
  obtain ⟨pH, hpHsep, hpH⟩ := hHSep F O bar g ρ a H hcomm χ hmin.1 hsep
    (fun q hq => (hKills F O bar g ρ a D P₀ hP ga H hH q).1 ((hmin.2 q).2 hq))
  obtain ⟨Sb, d, hdet, hM⟩ := hSim g (Option (𝓞 F))
    (fun o => Option.elim o H (fun c => ρ (a c))) (by
      rintro (_ | c) (_ | c')
      · rfl
      · exact (hcomm c').symm
      · exact hcomm c
      · show ρ (a c) * ρ (a c') = ρ (a c') * ρ (a c)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]) (by
      rintro (_ | c)
      · exact ⟨pH, hpHsep, hpH⟩
      · exact sep_of_integer (ρ.comp a) c)
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have hMs : ∀ c : 𝓞 F, ρ (a c) * Sb = Sb * Matrix.diagonal (d (some c)) := fun c => hM (some c)
  have hd : ∀ c : 𝓞 F, Sb⁻¹ * ρ (a c) * Sb = Matrix.diagonal (d (some c)) := by
    intro c
    rw [Matrix.mul_assoc, hMs c, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  have hent : ∀ (c : 𝓞 F) (i : Fin g), d (some c) i = (Sb⁻¹ * ρ (a c) * Sb) i i := by
    intro c i
    rw [hd c, Matrix.diagonal_apply_eq]
  let φ : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => d (some c) i
      map_one' := by
        show d (some 1) i = 1
        rw [hent, map_one, map_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hU, Matrix.one_apply_eq]
      map_mul' := fun c c' => by
        show d (some (c * c')) i = d (some c) i * d (some c') i
        have h1 := hd (c * c')
        have e : Sb⁻¹ * (ρ (a c) * ρ (a c')) * Sb
            = (Sb⁻¹ * ρ (a c) * Sb) * (Sb⁻¹ * ρ (a c') * Sb) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Sb (Sb⁻¹), Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
        rw [map_mul, map_mul, e, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        have h2 := congrFun (congrFun h1 i) i
        simpa using h2.symm
      map_zero' := by
        show d (some 0) i = 0
        rw [hent, map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
      map_add' := fun c c' => by
        show d (some (c + c')) i = d (some c) i + d (some c') i
        rw [hent, hent, hent, map_add, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] }
  have hτ := fun i => hExt F (φ i)
  choose ty hty using hτ
  refine ⟨Sb, ty, d none, ?_⟩
  refine ⟨hdet, fun c => ?_, hM none⟩
  rw [hMs c]
  congr 2
  funext i
  exact hty i c
